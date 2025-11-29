/**
 * @file commitment.cpp
 * @brief Implementation of LWE commitment scheme.
 *
 * Provides Module-LWE commitments backed by Microsoft SEAL primitives.
 */

#include "lambda_snark/commitment.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <cstdio>
#include <new>
#include <memory>
#include <sstream>
#include <utility>
#include <vector>

#include <seal/seal.h>

#ifndef HAVE_SEAL
#error "Lambda-SNARK requires Microsoft SEAL; configure the build with SEAL support."
#endif

#ifdef HAVE_SODIUM
#include <sodium.h>
#endif

struct LweContext {
    std::shared_ptr<seal::SEALContext> seal_ctx;
    std::unique_ptr<seal::PublicKey> pk;
    std::unique_ptr<seal::SecretKey> sk;
    std::unique_ptr<seal::Encryptor> encryptor;
    std::unique_ptr<seal::Decryptor> decryptor;
    std::unique_ptr<seal::BatchEncoder> encoder;
    std::unique_ptr<seal::Evaluator> evaluator;
    PublicParams params;
};

namespace {

LweCommitment* ciphertext_to_commitment(const seal::Ciphertext& cipher) {
    std::stringstream ss(std::ios::binary | std::ios::out | std::ios::in);
    cipher.save(ss);
    const std::string blob = ss.str();
    const std::size_t byte_len = blob.size();
    const std::size_t word_len = (byte_len + sizeof(uint64_t) - 1) / sizeof(uint64_t);

    auto comm = new LweCommitment;
    comm->len = word_len + 1;
    comm->data = new uint64_t[comm->len];

    comm->data[0] = static_cast<uint64_t>(byte_len);
    std::memset(comm->data + 1, 0, word_len * sizeof(uint64_t));
    std::memcpy(comm->data + 1, blob.data(), byte_len);

    return comm;
}

bool commitment_to_ciphertext(
    const LweContext* ctx,
    const LweCommitment* commitment,
    seal::Ciphertext& out_cipher
) {
    if (!ctx || !commitment || commitment->len < 1) {
        return false;
    }

    const uint64_t byte_len = commitment->data[0];
    const std::size_t available_bytes = (commitment->len - 1) * sizeof(uint64_t);
    if (byte_len == 0 || byte_len > available_bytes) {
        return false;
    }

    const char* blob_ptr = reinterpret_cast<const char*>(commitment->data + 1);
    std::string blob(blob_ptr, blob_ptr + byte_len);

    std::stringstream ss(std::ios::binary | std::ios::in | std::ios::out);
    ss.write(blob.data(), static_cast<std::streamsize>(blob.size()));
    ss.seekg(0);

    out_cipher.load(*ctx->seal_ctx, ss);
    return true;
}

seal::Plaintext encode_coefficient(const LweContext* ctx, uint64_t coeff) {
    const auto plain_modulus = ctx->seal_ctx->first_context_data()->parms().plain_modulus().value();
    coeff %= plain_modulus;

    std::vector<uint64_t> coeff_vec(ctx->encoder->slot_count(), coeff);
    seal::Plaintext plain;
    ctx->encoder->encode(coeff_vec, plain);
    return plain;
}

}  // namespace

extern "C" {

LweContext* lwe_context_create(const PublicParams* params) noexcept try {
    if (!params) return nullptr;

    auto ctx = std::make_unique<LweContext>();
    ctx->params = *params;

    seal::EncryptionParameters seal_params(seal::scheme_type::bfv);
    seal_params.set_poly_modulus_degree(params->ring_degree);
    seal_params.set_coeff_modulus(seal::CoeffModulus::BFVDefault(params->ring_degree));
    seal_params.set_plain_modulus(seal::PlainModulus::Batching(params->ring_degree, 20));

    ctx->seal_ctx = std::make_shared<seal::SEALContext>(seal_params);
    if (!ctx->seal_ctx) {
        return nullptr;
    }

    seal::KeyGenerator keygen(*ctx->seal_ctx);
    ctx->sk = std::make_unique<seal::SecretKey>(keygen.secret_key());
    ctx->pk = std::make_unique<seal::PublicKey>();
    keygen.create_public_key(*ctx->pk);

    ctx->encryptor = std::make_unique<seal::Encryptor>(*ctx->seal_ctx, *ctx->pk, *ctx->sk);
    ctx->decryptor = std::make_unique<seal::Decryptor>(*ctx->seal_ctx, *ctx->sk);
    ctx->encoder = std::make_unique<seal::BatchEncoder>(*ctx->seal_ctx);
    ctx->evaluator = std::make_unique<seal::Evaluator>(*ctx->seal_ctx);

    return ctx.release();
} catch (const std::exception& e) {
    std::fprintf(stderr, "lwe_context_create error: %s\n", e.what());
    return nullptr;
}

void lwe_context_free(LweContext* ctx) noexcept {
    delete ctx;
}

LweCommitment* lwe_commit(
    LweContext* ctx,
    const uint64_t* message,
    size_t msg_len,
    uint64_t /*seed*/
) noexcept try {
    if (!ctx || !message) return nullptr;

    const std::size_t slot_count = ctx->encoder->slot_count();
    std::vector<uint64_t> msg_vec(slot_count, 0);
    const std::size_t copy_len = std::min(msg_len, slot_count);
    std::copy_n(message, copy_len, msg_vec.begin());

    seal::Plaintext plain;
    ctx->encoder->encode(msg_vec, plain);

    seal::Ciphertext cipher;
    ctx->encryptor->encrypt_symmetric(plain, cipher);

    return ciphertext_to_commitment(cipher);
} catch (const std::exception& e) {
    std::fprintf(stderr, "lwe_commit error: %s\n", e.what());
    return nullptr;
} catch (...) {
    std::fprintf(stderr, "lwe_commit error: unknown exception\n");
    return nullptr;
}

void lwe_commitment_free(LweCommitment* comm) noexcept {
    if (!comm) return;
    if (comm->data) {
#ifdef HAVE_SODIUM
        sodium_memzero(comm->data, comm->len * sizeof(uint64_t));
#else
        std::memset(comm->data, 0, comm->len * sizeof(uint64_t));
#endif
        delete[] comm->data;
    }
    delete comm;
}

LweCommitment* lwe_commitment_clone(const LweCommitment* comm) noexcept {
    if (!comm || comm->len == 0 || !comm->data) {
        return nullptr;
    }

    auto clone = new (std::nothrow) LweCommitment;
    if (!clone) {
        return nullptr;
    }

    clone->len = comm->len;
    clone->data = new (std::nothrow) uint64_t[clone->len];
    if (!clone->data) {
        delete clone;
        return nullptr;
    }

    std::memcpy(clone->data, comm->data, clone->len * sizeof(uint64_t));
    return clone;
}

int lwe_verify_opening(
    const LweContext* ctx,
    const LweCommitment* commitment,
    const uint64_t* message,
    size_t msg_len,
    const LweOpening* /*opening*/
) noexcept try {
    if (!ctx || !commitment || !message) return -1;

    seal::Ciphertext cipher;
    if (!commitment_to_ciphertext(ctx, commitment, cipher)) {
        return -1;
    }

    seal::Plaintext plain;
    ctx->decryptor->decrypt(cipher, plain);

    std::vector<uint64_t> decoded;
    ctx->encoder->decode(plain, decoded);
    if (decoded.size() < msg_len) {
        return 0;
    }

    uint64_t diff = 0;
    for (size_t i = 0; i < msg_len; ++i) {
        diff |= (decoded[i] ^ message[i]);
    }

    return diff == 0 ? 1 : 0;
} catch (const std::exception& e) {
    std::fprintf(stderr, "lwe_verify_opening error: %s\n", e.what());
    return -1;
}

LweCommitment* lwe_linear_combine(
    const LweContext* ctx,
    const LweCommitment** commitments,
    const uint64_t* coeffs,
    size_t count
) noexcept try {
    if (!ctx || !commitments || !coeffs || count == 0) {
        return nullptr;
    }

    seal::Ciphertext accumulator;
    bool has_value = false;

    for (size_t i = 0; i < count; ++i) {
        if (!commitments[i]) {
            continue;
        }

        seal::Ciphertext term;
        if (!commitment_to_ciphertext(ctx, commitments[i], term)) {
            return nullptr;
        }

        seal::Plaintext coeff_plain = encode_coefficient(ctx, coeffs[i]);
        ctx->evaluator->multiply_plain_inplace(term, coeff_plain);

        if (!has_value) {
            accumulator = std::move(term);
            has_value = true;
        } else {
            ctx->evaluator->add_inplace(accumulator, term);
        }
    }

    if (!has_value) {
        return nullptr;
    }

    return ciphertext_to_commitment(accumulator);
} catch (const std::exception& e) {
    std::fprintf(stderr, "lwe_linear_combine error: %s\n", e.what());
    return nullptr;
}

}  // extern "C"
