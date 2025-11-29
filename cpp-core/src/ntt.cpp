/**
 * @file ntt.cpp
 * @brief Thin wrapper around Microsoft SEAL NTT primitives.
 */

#include "lambda_snark/ntt.h"
#include <cstdlib>
#include <cstdint>
#include <memory>
#include <new>

#include <seal/modulus.h>
#include <seal/memorymanager.h>
#include <seal/util/ntt.h>
#include <seal/util/uintarithsmallmod.h>

#ifndef HAVE_SEAL
#error "Lambda-SNARK requires Microsoft SEAL; configure the build with SEAL support."
#endif

struct NttContext {
    uint64_t modulus;
    uint32_t degree;
    seal::Modulus seal_modulus;
    std::unique_ptr<seal::util::NTTTables> tables;
};

extern "C" {

NttContext* ntt_context_create(uint64_t q, uint32_t n) noexcept {
    if (n == 0) return nullptr;

    auto ctx = new (std::nothrow) NttContext;
    if (!ctx) return nullptr;

    ctx->modulus = q;
    ctx->degree = n;

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

    try {
        seal::util::ntt_negacyclic_harvey(coeffs, *ctx->tables);
        return 0;
    } catch (...) {
        return -1;
    }
}

int ntt_inverse(
    const NttContext* ctx,
    uint64_t* evals,
    uint32_t n
) noexcept {
    if (!ctx || !evals || n != ctx->degree) return -1;

    try {
        seal::util::inverse_ntt_negacyclic_harvey(evals, *ctx->tables);
        return 0;
    } catch (...) {
        return -1;
    }
}

void ntt_mul_pointwise(
    const NttContext* ctx,
    uint64_t* result,
    const uint64_t* a,
    const uint64_t* b,
    uint32_t n
) noexcept {
    if (!ctx || !result || !a || !b) return;

    const auto& modulus = ctx->seal_modulus;
    for (uint32_t i = 0; i < n; ++i) {
        result[i] = seal::util::multiply_uint_mod(a[i], b[i], modulus);
    }
}

}  // extern "C"
