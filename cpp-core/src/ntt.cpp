/**
 * @file ntt.cpp
 * @brief NTT implementation using NTL (Number Theory Library).
 * 
 * @copyright Copyright (c) 2025 URPKS Contributors
 * @license Apache-2.0 OR MIT
 */

#include "lambda_snark/ntt.h"
/**
 * @file ntt.cpp
 * @brief Thin wrapper around Microsoft SEAL NTT primitives.
 */

#include "lambda_snark/ntt.h"
#include <cstdlib>
#include <cstdint>
#include <memory>
#include <new>

#ifdef HAVE_SEAL
#include <seal/modulus.h>
#include <seal/memorymanager.h>
#include <seal/util/ntt.h>
#include <seal/util/uintarithsmallmod.h>
#endif

struct NttContext {
    uint64_t modulus;
    uint32_t degree;
#ifdef HAVE_SEAL
    seal::Modulus seal_modulus;
    std::unique_ptr<seal::util::NTTTables> tables;
#else
    uint8_t stub;  // placeholder to avoid empty struct warnings
#endif
};

extern "C" {

NttContext* ntt_context_create(uint64_t q, uint32_t n) noexcept {
    if (n == 0) return nullptr;

    auto ctx = new (std::nothrow) NttContext;
    if (!ctx) return nullptr;

    ctx->modulus = q;
    ctx->degree = n;

#ifdef HAVE_SEAL
    try {
        // Validate input: SEAL expects power-of-two degree.
        if ((n & (n - 1)) != 0) {
            delete ctx;
            return nullptr;
        }

        ctx->seal_modulus = seal::Modulus(q);

        std::size_t coeff_power = 0;
        uint32_t temp = n;
        while (temp > 1) {
            temp >>= 1;
            ++coeff_power;
        }

        ctx->tables = std::make_unique<seal::util::NTTTables>(
            coeff_power,
            ctx->seal_modulus,
            seal::MemoryManager::GetPool()
        );
        if (!ctx->tables) {
            delete ctx;
            return nullptr;
        }
    } catch (...) {
        delete ctx;
        return nullptr;
    }
#endif

    return ctx;
}

void ntt_context_free(NttContext* ctx) noexcept {
    delete ctx;
}

int ntt_forward(
    const NttContext* ctx,
    uint64_t* coeffs,
    uint32_t n
) noexcept {
    if (!ctx || !coeffs || n != ctx->degree) return -1;

#ifdef HAVE_SEAL
    try {
        seal::util::ntt_negacyclic_harvey(coeffs, *ctx->tables);
        return 0;
    } catch (...) {
        return -1;
    }
#else
    (void)coeffs;
    return 0;
#endif
}

int ntt_inverse(
    const NttContext* ctx,
    uint64_t* evals,
    uint32_t n
) noexcept {
    if (!ctx || !evals || n != ctx->degree) return -1;

#ifdef HAVE_SEAL
    try {
        seal::util::inverse_ntt_negacyclic_harvey(evals, *ctx->tables);
        return 0;
    } catch (...) {
        return -1;
    }
#else
    (void)evals;
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

#ifdef HAVE_SEAL
    const auto& modulus = ctx->seal_modulus;
    for (uint32_t i = 0; i < n; ++i) {
        result[i] = seal::util::multiply_uint_mod(a[i], b[i], modulus);
    }
#else
    const uint64_t mod = ctx->modulus;
    for (uint32_t i = 0; i < n; ++i) {
        result[i] = static_cast<uint64_t>((static_cast<__uint128_t>(a[i]) * b[i]) % mod);
    }
#endif
}

}  // extern "C"
