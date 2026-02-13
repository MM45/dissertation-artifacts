# Specification Security

This directory contains the specification-level security proofs for XMSS
(`xmss/`) and SPHINCS<sup>+</sup> (`sphincsplus/`).  

The developments have been verified with [EasyCrypt release
r2026.02](https://github.com/EasyCrypt/easycrypt/releases/tag/r2026.02), using
SMT solvers Alt-Ergo 2.6.0 and Z3 4.13.4, as specified in `easycrypt.project`.

## Building, Running, and Testing

You can run/test this development either via Docker or natively (if you have the
correct EasyCrypt + solver installation).

### Prerequisites

- Docker approach:  
  - [Docker Engine](https://docs.docker.com/engine/install), installed and running.
- Native approach:  
  - [EasyCrypt (release r2026.02)](https://github.com/EasyCrypt/easycrypt/tree/r2026.02), installed and configured with the solvers listed below.
  - Alt-Ergo 2.6.0.
  - Z3 4.13.4.

For the native approach, the [EasyCrypt README.md for
r2026.02](https://github.com/EasyCrypt/easycrypt/blob/r2026.02/README.md)
describes installation and solver configuration. More detailed instructions are
provided in the
[INSTALL.md](https://github.com/EasyCrypt/easycrypt/blob/r2026.02/INSTALL.md).

### Docker

Run the default verification tests inside the Docker environment, either for
both developments or individually (in each case, the entire development is
verified; no additional dedicated test cases are defined):
```shell
make docker-check       # Both XMSS and SPHINCS+
make docker-check-xmss  # XMSS only
make docker-check-sp    # SPHINCS+ only
```

To explore and interact with the repository inside the container, start an interactive shell:
```shell
make docker-shell
```

This drops you into a shell inside the Docker image with the repository as the
working directory. From there you can run the same commands as in the native
approach (see below).

### Native

Run the default verification tests, either for both developments or individually
(in each case, the entire development is verified; no additional
dedicated test cases are defined).
```shell
make check          # Both XMSS and SPHINCS+
make check-xmss     # XMSS only
make check-sp       # SPHINCS+ only
```

Beyond running tests, these also store test reports in the `reports/` directory
of the respective development; this directory is created automatically if it
does not exist yet.  

Remove EasyCrypt’s cached verification artifacts (`.eco` files),
either across all developments or for an individual one:
```shell
make clean          # Both XMSS and SPHINCS+
make clean-xmss     # XMSS only
make clean-sp       # SPHINCS+ only
```

Additionally remove the respective `reports/` directory:
```shell
make clobber        # Both XMSS and SPHINCS+
make clobber-xmss   # XMSS only
make clobber-sp     # SPHINCS+ only
```

### Help with Make

All of the above uses `make` and, hence, goes through this directory's
`Makefile`. To list available targets and brief descriptions:
```shell
make help
```

`make` variables can be overridden (see the `Makefile` in this directory as well
as those in `xmss/` and `sphincsplus/`). This allows customization of the setup
(e.g., binary paths) or adjustment of parallelism to speed up verification.  

Note, however, that modifying these parameters may affect stability. In
particular, increased parallelism can trigger solver timeouts or related
failures. Unexpected verification failures may therefore occur when deviating
from the default configuration.
