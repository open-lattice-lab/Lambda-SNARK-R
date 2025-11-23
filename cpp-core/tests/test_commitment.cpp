/**
 * @file test_commitment.cpp
 * @brief Unit tests for the LWE commitment API.
 */

#include "lambda_snark/commitment.h"
#include <gtest/gtest.h>
#include <vector>

class CommitmentTest : public ::testing::Test {
protected:
    void SetUp() override {
        params.profile = PROFILE_RING_B;
        params.security_level = 128;
        params.modulus = 12289;
        params.ring_degree = 4096;  // SEAL requires power-of-2 >= 1024
        params.module_rank = 2;
        params.sigma = 3.19;
        
        ctx = lwe_context_create(&params);
        ASSERT_NE(ctx, nullptr);
    }
    
    void TearDown() override {
        lwe_context_free(ctx);
    }
    
    PublicParams params;
    LweContext* ctx = nullptr;
};

TEST_F(CommitmentTest, CreateAndFree) {
    // Context already created in SetUp
    EXPECT_NE(ctx, nullptr);
}

TEST_F(CommitmentTest, CommitBasic) {
    uint64_t message[] = {1, 2, 3, 4};
    size_t msg_len = 4;
    
    auto comm = lwe_commit(ctx, message, msg_len, 0x1234);
    ASSERT_NE(comm, nullptr);
    EXPECT_GT(comm->len, 0);
    EXPECT_NE(comm->data, nullptr);
    
    lwe_commitment_free(comm);
}

TEST_F(CommitmentTest, CommitBinding) {
    // Binding property: different messages → different commitments (with high probability)
    uint64_t msg1[] = {1, 2, 3};
    uint64_t msg2[] = {4, 5, 6};
    size_t msg_len = 3;
    
    auto comm1 = lwe_commit(ctx, msg1, msg_len, 0);
    auto comm2 = lwe_commit(ctx, msg2, msg_len, 0);
    
    ASSERT_NE(comm1, nullptr);
    ASSERT_NE(comm2, nullptr);
    ASSERT_GT(comm1->len, 0);
    ASSERT_GT(comm2->len, 0);
    
    // Different messages → commitments should differ (with overwhelming probability)
    bool different = false;
    for (size_t i = 0; i < comm1->len; ++i) {
        if (comm1->data[i] != comm2->data[i]) {
            different = true;
            break;
        }
    }
    EXPECT_TRUE(different) << "Commitments to different messages should differ";
    
    lwe_commitment_free(comm1);
    lwe_commitment_free(comm2);
}

TEST_F(CommitmentTest, CommitDifferentMessages) {
    uint64_t msg1[] = {1, 2, 3};
    uint64_t msg2[] = {4, 5, 6};
    uint64_t seed = 0x1234;
    
    auto comm1 = lwe_commit(ctx, msg1, 3, seed);
    auto comm2 = lwe_commit(ctx, msg2, 3, seed);
    
    ASSERT_NE(comm1, nullptr);
    ASSERT_NE(comm2, nullptr);
    
    // Different messages => different commitments (with high probability)
    bool different = false;
    for (size_t i = 0; i < std::min(comm1->len, comm2->len); ++i) {
        if (comm1->data[i] != comm2->data[i]) {
            different = true;
            break;
        }
    }
    EXPECT_TRUE(different) << "Commitments should differ for different messages";
    
    lwe_commitment_free(comm1);
    lwe_commitment_free(comm2);
}

TEST_F(CommitmentTest, NullPointerHandling) {
    // Null context
    auto comm = lwe_commit(nullptr, nullptr, 0, 0);
    EXPECT_EQ(comm, nullptr);
    
    // Null message
    comm = lwe_commit(ctx, nullptr, 10, 0);
    EXPECT_EQ(comm, nullptr);
    
    // Free null commitment (should not crash)
    lwe_commitment_free(nullptr);
}

TEST_F(CommitmentTest, VerifyOpeningMatchesMessage) {
    uint64_t message[] = {7, 11, 13, 17};
    const size_t msg_len = std::size(message);

    auto comm = lwe_commit(ctx, message, msg_len, 0);
    ASSERT_NE(comm, nullptr);

    uint64_t randomness = 0;
    LweOpening opening{&randomness, 1};

    EXPECT_EQ(lwe_verify_opening(ctx, comm, message, msg_len, &opening), 1);

    std::vector<uint64_t> wrong(message, message + msg_len);
    wrong[1] ^= 1U;
    EXPECT_EQ(lwe_verify_opening(ctx, comm, wrong.data(), msg_len, &opening), 0);

    lwe_commitment_free(comm);
}

TEST_F(CommitmentTest, LinearCombinationProducesExpectedCommitment) {
    const size_t msg_len = 4;
    uint64_t msg1[msg_len] = {1, 2, 3, 4};
    uint64_t msg2[msg_len] = {5, 6, 7, 8};

    auto comm1 = lwe_commit(ctx, msg1, msg_len, 0);
    auto comm2 = lwe_commit(ctx, msg2, msg_len, 0);
    ASSERT_NE(comm1, nullptr);
    ASSERT_NE(comm2, nullptr);

    const LweCommitment* inputs[] = {comm1, comm2};
    uint64_t coeffs[] = {2, 3};

    auto combined = lwe_linear_combine(ctx, inputs, coeffs, 2);
    ASSERT_NE(combined, nullptr);

    uint64_t expected[msg_len];
    for (size_t i = 0; i < msg_len; ++i) {
        expected[i] = coeffs[0] * msg1[i] + coeffs[1] * msg2[i];
    }

    uint64_t randomness = 0;
    LweOpening opening{&randomness, 1};

    EXPECT_EQ(lwe_verify_opening(ctx, combined, expected, msg_len, &opening), 1);

    expected[0] += 1;
    EXPECT_EQ(lwe_verify_opening(ctx, combined, expected, msg_len, &opening), 0);

    lwe_commitment_free(comm1);
    lwe_commitment_free(comm2);
    lwe_commitment_free(combined);
}
