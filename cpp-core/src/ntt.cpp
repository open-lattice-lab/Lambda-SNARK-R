/**
 * @file ntt.cpp
 * @brief NTT implementation using NTL (Number Theory Library).
 * 
 * @copyright Copyright (c) 2025 URPKS Contributors
 * @license Apache-2.0 OR MIT
 */

#include "lambda_snark/ntt.h"
#include <cstdlib>
#include <cstring>

#ifdef HAVE_NTL
#include <NTL/ZZ.h>
#include <NTL/ZZ_p.h>
#include <NTL/ZZ_pX.h>
#include <NTL/vector.h>

// Helper: compute modular exponentiation (base^exp mod mod)
static uint64_t mod_pow(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t result = 1;
    base %= mod;
    while (exp > 0) {
        if (exp & 1) {
            result = (static_cast<__uint128_t>(result) * base) % mod;
        }
        base = (static_cast<__uint128_t>(base) * base) % mod;
        exp >>= 1;
    }
    return result;
}

// Helper: find primitive n-th root of unity modulo q
// For q=12289, n=256: ω^256 ≡ 1 (mod 12289)
static uint64_t find_primitive_root(uint64_t q, uint32_t n) {
    // For q=12289 (prime), φ(q)=q-1=12288=2^8*48
    // We need ω such that ω^n=1 but ω^(n/2)≠1
    // Generator for Z_q*: try small values
    for (uint64_t g = 2; g < q; ++g) {
        uint64_t w = mod_pow(g, (q - 1) / n, q);
        // Check if w is primitive n-th root: w^n=1, w^(n/2)≠1
        if (mod_pow(w, n, q) == 1 && mod_pow(w, n / 2, q) != 1) {
            return w;
        }
    }
    return 0;  // Failed to find (should never happen for valid q)
}

// Helper: bit-reverse index for Cooley-Tukey
static uint32_t bit_reverse(uint32_t x, uint32_t log_n) {
    uint32_t result = 0;
    for (uint32_t i = 0; i < log_n; ++i) {
        result = (result << 1) | (x & 1);
        x >>= 1;
    }
    return result;
}
#endif

// Internal NTT context
struct NttContext {
    uint64_t modulus;
    uint32_t degree;
    uint32_t log_degree;  // log2(degree)
    
#ifdef HAVE_NTL
    bool ntl_initialized;
    uint64_t omega;          // Primitive n-th root of unity
    uint64_t* twiddle_fwd;   // Forward twiddle factors
    uint64_t* twiddle_inv;   // Inverse twiddle factors
    uint64_t inv_n;          // n^{-1} mod q for normalization
#else
    uint64_t* twiddle_factors;  // Precomputed roots of unity (stub mode)
#endif
};

extern "C" {

NttContext* ntt_context_create(uint64_t q, uint32_t n) noexcept {
    auto ctx = new (std::nothrow) NttContext;
    if (!ctx) return nullptr;
    
    ctx->modulus = q;
    ctx->degree = n;
    
    // Compute log2(n)
    uint32_t log_n = 0;
    uint32_t tmp = n;
    while (tmp > 1) {
        log_n++;
        tmp >>= 1;
    }
    ctx->log_degree = log_n;
    
    // Check n is power of 2
    if ((1U << log_n) != n) {
        delete ctx;
        return nullptr;
    }
    
#ifdef HAVE_NTL
    // Initialize NTL modulus
    try {
        NTL::ZZ_p::init(NTL::ZZ(static_cast<long>(q)));
        ctx->ntl_initialized = true;
        
        // Find primitive n-th root of unity
        ctx->omega = find_primitive_root(q, n);
        if (ctx->omega == 0) {
            delete ctx;
            return nullptr;
        }
        
        // Precompute twiddle factors
        ctx->twiddle_fwd = new (std::nothrow) uint64_t[n];
        ctx->twiddle_inv = new (std::nothrow) uint64_t[n];
        if (!ctx->twiddle_fwd || !ctx->twiddle_inv) {
            delete[] ctx->twiddle_fwd;
            delete[] ctx->twiddle_inv;
            delete ctx;
            return nullptr;
        }
        
        // Forward twiddles: ω^i
        for (uint32_t i = 0; i < n; ++i) {
            ctx->twiddle_fwd[i] = mod_pow(ctx->omega, i, q);
        }
        
        // Inverse twiddles: ω^{-i} = ω^{n-i}
        for (uint32_t i = 0; i < n; ++i) {
            ctx->twiddle_inv[i] = mod_pow(ctx->omega, n - i, q);
        }
        
        // Compute n^{-1} mod q using Fermat's little theorem: n^{-1} = n^{q-2} mod q
        ctx->inv_n = mod_pow(n, q - 2, q);
        
    } catch (...) {
        delete ctx;
        return nullptr;
    }
#else
    // Stub mode: allocate twiddle factors
    ctx->twiddle_factors = new (std::nothrow) uint64_t[n];
    if (!ctx->twiddle_factors) {
        delete ctx;
        return nullptr;
    }
    // Stub: zero initialization
    std::memset(ctx->twiddle_factors, 0, n * sizeof(uint64_t));
#endif
    
    return ctx;
}

void ntt_context_free(NttContext* ctx) noexcept {
    if (ctx) {
#ifdef HAVE_NTL
        delete[] ctx->twiddle_fwd;
        delete[] ctx->twiddle_inv;
#else
        delete[] ctx->twiddle_factors;
#endif
        delete ctx;
    }
}

int ntt_forward(
    const NttContext* ctx,
    uint64_t* coeffs,
    uint32_t n
) noexcept {
    if (!ctx || !coeffs || n != ctx->degree) return -1;
    
#ifdef HAVE_NTL
    try {
        const uint64_t q = ctx->modulus;
        const uint32_t log_n = ctx->log_degree;
        
        // Bit-reversal permutation
        for (uint32_t i = 0; i < n; ++i) {
            uint32_t j = bit_reverse(i, log_n);
            if (i < j) {
                std::swap(coeffs[i], coeffs[j]);
            }
        }
        
        // Cooley-Tukey butterfly iterations
        for (uint32_t s = 1; s <= log_n; ++s) {
            uint32_t m = 1U << s;        // Group size: 2, 4, 8, ..., n
            uint32_t m_half = m >> 1;    // Half group size
            uint32_t step = n / m;       // Twiddle step
            
            for (uint32_t k = 0; k < n; k += m) {
                for (uint32_t j = 0; j < m_half; ++j) {
                    uint64_t t = (static_cast<__uint128_t>(ctx->twiddle_fwd[step * j]) * 
                                  coeffs[k + j + m_half]) % q;
                    uint64_t u = coeffs[k + j];
                    
                    coeffs[k + j] = (u + t) % q;
                    coeffs[k + j + m_half] = (u >= t) ? (u - t) : (u + q - t);
                }
            }
        }
        
        return 0;
    } catch (...) {
        return -1;
    }
#else
    // Stub: identity transform
    return 0;
#endif
}

int ntt_inverse(
    const NttContext* ctx,
    uint64_t* evals,
    uint32_t n
) noexcept {
    if (!ctx || !evals || n != ctx->degree) return -1;
    
#ifdef HAVE_NTL
    try {
        const uint64_t q = ctx->modulus;
        const uint32_t log_n = ctx->log_degree;
        
        // Bit-reversal permutation
        for (uint32_t i = 0; i < n; ++i) {
            uint32_t j = bit_reverse(i, log_n);
            if (i < j) {
                std::swap(evals[i], evals[j]);
            }
        }
        
        // Inverse Cooley-Tukey (use inverse twiddles)
        for (uint32_t s = 1; s <= log_n; ++s) {
            uint32_t m = 1U << s;
            uint32_t m_half = m >> 1;
            uint32_t step = n / m;
            
            for (uint32_t k = 0; k < n; k += m) {
                for (uint32_t j = 0; j < m_half; ++j) {
                    uint64_t t = (static_cast<__uint128_t>(ctx->twiddle_inv[step * j]) * 
                                  evals[k + j + m_half]) % q;
                    uint64_t u = evals[k + j];
                    
                    evals[k + j] = (u + t) % q;
                    evals[k + j + m_half] = (u >= t) ? (u - t) : (u + q - t);
                }
            }
        }
        
        // Normalize by n^{-1}
        for (uint32_t i = 0; i < n; ++i) {
            evals[i] = (static_cast<__uint128_t>(evals[i]) * ctx->inv_n) % q;
        }
        
        return 0;
    } catch (...) {
        return -1;
    }
#else
    // Stub: identity transform
    return 0;
#endif
}

void ntt_mul_pointwise(
    const NttContext* ctx,
    uint64_t* result,
    const uint64_t* a,
    const uint64_t* b,
    uint32_t n
) noexcept {
    if (!ctx || !result || !a || !b) return;
    
    // Pointwise multiplication mod q
    for (uint32_t i = 0; i < n; ++i) {
        // TODO: Use Barrett reduction for efficiency
        result[i] = (static_cast<__uint128_t>(a[i]) * b[i]) % ctx->modulus;
    }
}

}  // extern "C"
