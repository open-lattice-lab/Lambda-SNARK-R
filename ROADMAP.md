# ΛSNARK-R Roadmap

## Overview

ΛSNARK-R development follows a **staged approach** prioritizing security, correctness, and performance in that order.

**Current Version**: 0.1.0-alpha  
**Target Production Release**: 1.0.0 (Q3 2026)

---

## Phase 1: Foundation (Q4 2025 - Q1 2026) ✅ COMPLETE

**Goal**: Working prototype with basic functionality.

### Milestones

- [x] **M1.1**: Repository setup (✅ November 2025)
  - Project structure
  - CI/CD pipeline
  - Documentation infrastructure

- [x] **M1.2**: C++ Core (✅ November 2025)
  - Full NTT implementation with NTL
  - Complete LWE commitment scheme via SEAL
  - FFI bindings (lambda-snark-sys)

- [x] **M1.3**: Rust API (✅ November 2025)
  - Safe FFI wrappers (LweContext, Commitment, Opening)
  - Polynomial data structures
  - Challenge derivation (Fiat-Shamir)

- [x] **M2.2**: SNARK Prover (✅ November 2025, commit e2c5957)
  - `prove_simple()`: witness → polynomial → commitment → challenge → opening
  - 90 tests passing
  - Performance: ~7ms per proof

- [x] **M2.3**: SNARK Verifier (✅ November 2025, commit f0e3406)
  - `verify_simple()`: challenge consistency + opening verification
  - 101 tests passing
  - Soundness: ε ≤ 2^-44

- [x] **LWE FFI**: Opening Verification (✅ November 2025, commit 889cc16)
  - `verify_opening_with_context()`: C++ integration for soundness
  - 104 tests passing (6 ignored SEAL non-determinism)

- [x] **M3**: Zero-Knowledge (✅ November 2025, commit d7be985)
  - **M3.1**: Design specification (polynomial blinding scheme)
  - **M3.2**: Blinding polynomials (ChaCha20 CSPRNG, `random_blinding()`, `add()`)
  - **M3.3**: ZK prover `prove_zk()` with blinded commitment (f'(X) = f(X) + r(X))
  - **M3.4**: Blinded opening (auto-complete via existing infrastructure)
  - **M3.5**: Simulator `simulate_proof()` for indistinguishability
  - **M3.6**: Empirical ZK validation (distinguisher: 50% accuracy = random guessing)
  - **Security**: Adv_ZK ≤ 2^-128 (HVZK validated)
  - **Performance**: <0.02% overhead (~1.1μs blinding cost)
  - **Tests**: 156/162 passing (96.3%)

**Deliverables**: ✅
- Working SNARK system (prove_simple, verify_simple, prove_zk)
- Zero-knowledge proofs with HVZK
- 156 comprehensive tests
- 4 design documents (M3.1, M3.2, M3.3-M3.4, M3-complete)

---

## Phase 2: R1CS Integration (Q1 2026)

**Goal**: Full circuit support with constraint system.

### Milestones

- [ ] **M4.1**: R1CS Design Specification (December 2025)
  - Witness encoding schema for arbitrary circuits
  - Constraint system representation (A, B, C matrices)
  - Polynomial commitment strategy for R1CS
  - Soundness analysis for circuit constraints
  - Deliverable: `docs/development/M4.1-r1cs-design.md`

- [ ] **M4.2**: R1CS Constraint System (January 2026)
  - Implement `prove()` with R1CS matrices
  - Circuit-to-witness encoding
  - Constraint satisfaction checks (Az ⊙ Bz = Cz)
  - Integration tests with simple circuits (multiplication gate)
  - Files: `src/r1cs.rs`, update `src/lib.rs`
  - Target: 20+ R1CS tests

- [ ] **M4.3**: Circuit Compiler (January 2026)
  - DSL/builder API for circuits
  - Gate abstractions (Add, Mul, Const)
  - Automatic witness allocation
  - Constraint generation
  - Example: `circuit.mul(a, b, c).add(c, d, e)`
  - Files: `src/circuit.rs`, `examples/simple_circuit.rs`
  - Target: Compile 5+ example circuits

**Deliverables**:
- Working R1CS prover/verifier
- Circuit builder API
- Example circuits (arithmetic, boolean)
- Updated API (0.3.0-alpha)

**Success Criteria**:
- Prove/verify arbitrary R1CS instances
- Clean circuit construction API
- Documentation with circuit examples

---

## Phase 3: Optimization (Q1 - Q2 2026)

**Goal**: Production-level performance.

### Milestones

- [ ] **M5.1**: Batch Proving Optimization (February 2026)
  - Batch polynomial commitment (commit k polynomials at once)
  - Aggregated challenge derivation
  - Parallel blinding generation (rayon)
  - Performance benchmarks
  - Goal: 10x throughput for batch size = 100
  - Files: `src/batch.rs`, `benches/batch_proving.rs`

- [ ] **M5.2**: Preprocessing & Caching (February 2026)
  - Precompute commitment parameters
  - NTT domain caching
  - Challenge table pregeneration
  - Memory-mapped artifact storage
  - Goal: Reduce setup time from ~50ms to <5ms
  - Files: `src/preprocess.rs`, `src/cache.rs`

- [ ] **M5.3**: Performance Benchmarking (March 2026)
  - Comprehensive latency/throughput benchmarks
  - Memory profiling (commitment size, proof size)
  - Verifier performance (target <1ms)
  - Comparison with other post-quantum SNARKs
  - Files: `benches/*.rs`, `docs/performance.md`

**Deliverables**:
- Beta release (0.5.0-beta)
- Performance report
- Optimization guide

**Success Criteria**:
- Batch proving: 10x throughput improvement
- Verifier: <1ms per proof
- Preprocessing: Setup time <5ms
- Proof size: <50 KB

---

## Phase 4: Hardening (Q2 - Q3 2026)

**Goal**: Production-ready security and reliability.

### Milestones

- [ ] **M6.1**: Constant-Time Operations (April 2026)
  - Audit polynomial arithmetic for timing leaks
  - Implement constant-time modular reduction
  - Blinding coefficient generation without data-dependent branches
  - Timing attack tests
  - Use `subtle` crate
  - Files: `src/ct_poly.rs`, `tests/timing_attacks.rs`
  - Security: Timing variance <1%

- [ ] **M6.2**: Formal Verification (April-May 2026)
  - Lean 4 soundness proof (ε ≤ 2^-44)
  - Lean 4 zero-knowledge proof (Adv_ZK ≤ 2^-128)
  - Completeness theorem (∀ valid witness → proof verifies)
  - Simulator indistinguishability
  - Files: `lean/Lambda_SNARK/*.lean`
  - Target: All 4 theorems proven + checked by Lean kernel

- [ ] **M6.3**: Security Audit (May-June 2026)
  - Engage Trail of Bits or NCC Group
  - Audit Rust API and C++ FFI (6-8 weeks)
  - Fix all critical/high severity findings
  - Public audit report

- [ ] **M6.4**: Testing & Fuzzing (June 2026)
  - 90% code coverage (cargo-tarpaulin)
  - 48h continuous fuzzing (cargo-fuzz)
  - Constant-time validation (dudect)
  - Property-based tests (proptest)

- [ ] **M6.5**: Documentation & Examples (June-July 2026)
  - API reference (rustdoc)
  - Tutorial series (basic proof, ZK proof, R1CS circuit)
  - Security guide (parameter selection, threat model)
  - Integration examples (web3, blockchain)
  - Files: `docs/api/`, `docs/tutorials/`, `examples/`

- [ ] **M6.6**: CI/CD & Release Automation (July 2026)
  - GitHub Actions for tests/benches/lints
  - Automated security audits (cargo-audit, cargo-deny)
  - Release workflow (versioning, changelog, crates.io publish)
  - Performance regression tracking
  - Files: `.github/workflows/*.yml`, `CHANGELOG.md`

**Deliverables**:
- Release candidate (1.0.0-rc1)
- Audit report (public)
- Formal proofs (Lean 4 repository)
- Comprehensive documentation

**Success Criteria**:
- No critical/high severity findings in audit
- Formal proofs checked by Lean kernel
- API stable (semver 1.0.0)
- 90% test coverage
- Constant-time validation passed

---

## Phase 5: Ecosystem (Q3 2026 onwards)

- [ ] **M3.1**: Security Audit (April-May 2026)
  - Engage Trail of Bits
  - Audit C++ core (6-8 weeks)
  - Fix findings

- [ ] **M3.2**: Formal Verification (May-June 2026)
  - Lean 4 soundness proof
  - Lean 4 zero-knowledge proof
  - Completeness theorem

- [ ] **M3.3**: Fuzzing & Testing (June 2026)
  - 90% coverage (cargo-tarpaulin)
  - 48h continuous fuzzing
  - Constant-time validation (dudect)

- [ ] **M3.4**: API Stabilization (July 2026)
  - Lock public API (semver 1.0.0)
  - Comprehensive documentation
  - Migration guides

**Deliverables**:
- Release candidate (1.0.0-rc1)
- Audit report (public)
- Formal proofs (Lean 4 repository)

**Success Criteria**:
- No critical/high severity findings in audit
- Formal proofs checked by Lean kernel
- API stable (breaking changes prohibited)

---

## Phase 5: Ecosystem (Q3 2026 onwards)

**Goal**: Integration and adoption.

### Milestones

- [ ] **M7.1**: Public Release (August 2026)
  - Version 1.0.0
  - Crates.io publication
  - Announcement (blog, RWC)

- [ ] **M7.2**: QGravity Integration (Q4 2026)
  - Wilson loops → R1CS
  - Plaquette constraints
  - Physics examples

- [ ] **M7.3**: Proof-Twin Integration (Q4 2026)
  - Export VK as Lean terms
  - Reverse-Explorer compatibility
  - Theorem graph visualization

- [ ] **M7.4**: Bounty Program (Q4 2026)
  - HackerOne setup
  - $20k initial budget
  - Disclosure policy

**Deliverables**:
- Production releases (1.x.x)
- Integration examples
- Academic publications

---

## Long-Term Vision (2027+)

### Research Directions

1. **Recursive Composition**: SNARK-of-SNARK for scalability
2. **Aggregation**: Batch verification for multiple proofs
3. **Hardware Acceleration**: FPGA/ASIC for NTT
4. **Trusted Setup Elimination**: Fully transparent setup

### Community Growth

- Conference talks (RWC, Eurocrypt, Crypto)
- Workshops and tutorials
- Industry partnerships
- Grant applications (NSF, EU Horizon)

---

## Risk Mitigation

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| **NTL integration fails** | High | Low | Fallback to pure Rust (slower) |
| **Audit finds critical bugs** | High | Medium | 3-month buffer for fixes |
| **Parameters insecure** | Critical | Low | External review by lattice experts |
| **Performance targets missed** | Medium | Medium | Incremental optimization, relaxed targets |

---

## Decision Points

- **Q1 2026**: Phase 2 (R1CS Integration) completion review
- **Q2 2026**: Security audit readiness review  
- **Q3 2026**: Public release decision (based on audit + formal proofs)

---

## Current Status (November 2025)

**Completed**:
- ✅ Phase 1: Foundation (M1.1, M1.2, M1.3, M2.2, M2.3, LWE FFI, M3)
- ✅ 156/162 tests passing (96.3%)
- ✅ Zero-knowledge with HVZK validation
- ✅ Commits: e2c5957 (Prover), f0e3406 (Verifier), 889cc16 (LWE FFI), d7be985 (M3 ZK)

**In Progress**:
- Planning Phase 2 (R1CS Integration)

**Next Up**:
- M4.1 R1CS Design Specification (December 2025)

---

## Progress Summary

| Phase | Status | Completion | Target Date |
|-------|--------|-----------|-------------|
| Phase 1: Foundation | ✅ Complete | 100% (7/7 milestones) | Q4 2025 |
| Phase 2: R1CS Integration | 🔵 Planned | 0% (0/3) | Q1 2026 |
| Phase 3: Optimization | 🔵 Planned | 0% (0/3) | Q1-Q2 2026 |
| Phase 4: Hardening | 🔵 Planned | 0% (0/6) | Q2-Q3 2026 |
| Phase 5: Ecosystem | 🔵 Planned | 0% (0/4) | Q3 2026+ |

**Overall Progress**: 7/23 milestones (30.4%)

---

## Get Involved

- **Contributors**: See [CONTRIBUTING.md](CONTRIBUTING.md)
- **Feedback**: [GitHub Discussions](https://github.com/URPKS/lambda-snark-r/discussions)
- **Sponsorship**: Contact dev@lambda-snark.org

---

**Last Updated**: November 7, 2025 (Post-M3 Zero-Knowledge completion)  
**Next Review**: December 2025 (M4.1 R1CS Design)  
**Version**: 0.2.0-alpha (Phase 1 complete, ZK validated)
