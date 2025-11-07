/**
 * @file ffi.cpp
 * @brief FFI utilities and wrapper functions.
 * 
 * @copyright Copyright (c) 2025 URPKS Contributors
 * @license Apache-2.0 OR MIT
 */

#include "lambda_snark/types.h"
#include "lambda_snark/commitment.h"
#include "lambda_snark/r1cs.h"
#include <cstring>
#include <new>

extern "C" {

/**
 * @brief Create R1CS constraint system from sparse matrices.
 * 
 * @param A Left matrix (sparse)
 * @param B Right matrix (sparse)
 * @param C Output matrix (sparse)
 * @param modulus Field modulus q
 * @param out_r1cs Output R1CS handle
 * @return Error code
 */
LambdaSnarkError lambda_snark_r1cs_create(
    const SparseMatrix* A,
    const SparseMatrix* B,
    const SparseMatrix* C,
    uint64_t modulus,
    void** out_r1cs)
{
    if (!A || !B || !C || !out_r1cs) {
        return LAMBDA_SNARK_ERR_NULL_PTR;
    }
    
    try {
        auto* r1cs = new lambda_snark::R1CS(*A, *B, *C, modulus);
        *out_r1cs = r1cs;
        return LAMBDA_SNARK_OK;
    } catch (const std::invalid_argument&) {
        return LAMBDA_SNARK_ERR_INVALID_PARAMS;
    } catch (const std::bad_alloc&) {
        return LAMBDA_SNARK_ERR_ALLOC_FAILED;
    } catch (...) {
        return LAMBDA_SNARK_ERR_CRYPTO_FAILED;
    }
}

/**
 * @brief Validate witness against R1CS constraints.
 * 
 * @param r1cs R1CS handle
 * @param witness Witness vector
 * @param out_valid Output: true if valid
 * @return Error code
 */
LambdaSnarkError lambda_snark_r1cs_validate_witness(
    void* r1cs,
    const R1CSWitness* witness,
    bool* out_valid)
{
    if (!r1cs || !witness || !out_valid) {
        return LAMBDA_SNARK_ERR_NULL_PTR;
    }
    
    try {
        auto* r = static_cast<lambda_snark::R1CS*>(r1cs);
        std::vector<uint64_t> w(witness->values, witness->values + witness->len);
        *out_valid = r->validate_witness(w);
        return LAMBDA_SNARK_OK;
    } catch (const std::invalid_argument&) {
        return LAMBDA_SNARK_ERR_INVALID_PARAMS;
    } catch (...) {
        return LAMBDA_SNARK_ERR_CRYPTO_FAILED;
    }
}

/**
 * @brief Free R1CS handle.
 * 
 * @param r1cs R1CS handle
 */
void lambda_snark_r1cs_free(void* r1cs) {
    if (r1cs) {
        delete static_cast<lambda_snark::R1CS*>(r1cs);
    }
}

/**
 * @brief Get number of constraints in R1CS.
 */
uint32_t lambda_snark_r1cs_num_constraints(void* r1cs) {
    if (!r1cs) return 0;
    return static_cast<lambda_snark::R1CS*>(r1cs)->num_constraints();
}

/**
 * @brief Get number of variables in R1CS.
 */
uint32_t lambda_snark_r1cs_num_variables(void* r1cs) {
    if (!r1cs) return 0;
    return static_cast<lambda_snark::R1CS*>(r1cs)->num_variables();
}

}  // extern "C"

// Additional FFI helper functions can go here
