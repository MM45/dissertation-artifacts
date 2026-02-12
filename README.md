# Dissertation Artifacts

This repository accompanies the dissertation *Toward Machine-Checked
Post-Quantum Cryptography: Digital Signature Schemes and Key Encapsulation
Mechanisms* by M.C.F.H.P. Meijers and contains the complete set of underlying
artifacts.   

Specifically, it provides consolidated snapshots of the
developments corresponding to the original papers included in the dissertation
and serves as the single archival reference point for all formalizations and
implementations produced as part of this work, excluding some early components
that were later integrated in [EasyCrypt's standard
library](https://github.com/EasyCrypt/easycrypt/theories)).  

Release `v1.0` (the current version) is archived on Zenodo and assigned a DOI:
_TODO create and insert DOI_

## Mapping the Artifacts

The artifacts contained in this repository correspond to specific dissertation
chapters and original publications/repositories.

- `impleqv/xmss/`:
    - Scope: Implementation and functional correctness of XMSS
    - Dissertation chapter: Chapter 4 — XMSS
    - Original paper: *Completing the Chain: Verified Implementations of Hash-Based Signatures and Their Security*
    - Original repository: https://github.com/formosa-crypto/formosa-xmss
- `specsec/xmss/`:
    - Scope: Specification-level security proof for XMSS
    - Dissertation chapter: Chapter 4 — XMSS
    - Original paper: *Machine-Checked Security for XMSS as in RFC 8391 and SPHINCS<sup>+</sup>*
    - Original repository: https://github.com/MM45/FV-XMSS-EC
- `specsec/sphincsplus/`
    - Scope: Specification-level security proof for SPHINCS<sup>+</sup>
    - Dissertation chapter: Chapter 5 — SPHINCS<sup>+</sup>
    - Original paper: *A Tight Security Proof for SPHINCS⁺, Formally Verified*
    - Original repository: https://github.com/MM45/FV-SPHINCSPLUS-EC

# Navigating this Repository

The primary purpose of this repository is long-term archival of a working,
self-contained distribution of all dissertation artifacts. Each artifact
(or closely related set of artifacts) is structured to support reproducible
verification.  

In particular, the top-level directories `specsec/` and `impleqv/` each contain:
- a `Dockerfile` defining a consistent verification environment,
- a `Makefile` providing standardized verification targets, and
- a dedicated `README` with usage instructions.

The respective `README` files also document the primary dependencies and either
provide installation instructions or reference external documentation,
facilitating native verification where desired.

# Licenses

The original artifacts do not share a uniform license:

- The specification-level security developments (`specsec/`) are licensed under MIT.
- The implementation and functional correctness development (`impleqv/`) is licensed under Apache License 2.0.

Each artifact retains its original license. The applicable license for any
given file is the one located in the closest parent directory.  

The repository root includes an MIT license; however, all substantive material
is governed by the licenses contained in the respective subdirectories.
