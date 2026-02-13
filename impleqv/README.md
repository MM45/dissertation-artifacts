# Implementation Functional Equivalence

This directory contains the implementation and functional equivalence proofs for
XMSS (`xmss/`).  

The development has been verified with
[EasyCrypt r2026.02](https://github.com/EasyCrypt/easycrypt/releases/tag/r2026.02),
using the EasyCrypt library distributed with
[Jasmin’s compiler release 2025.06](https://gitlab.com/jasmin-lang/jasmin-compiler/-/tree/release-2025.06),
and the SMT solvers Alt-Ergo 2.6.0, CVC4 1.8, and Z3 4.13.4, as specified in
`easycrypt.project`.

## Comparison to Original Artifact

The original development additionally included unit tests and benchmarking
suites for the concrete implementation. These components were primarily
developed by co-authors and are not central contributions of the dissertation;
accordingly, they are excluded here.

The implementation itself was likewise largely developed by co-authors and is
not the primary focus of this work. It is nevertheless included
(`xmss/ref-jasmin/`) for reference and to facilitate verification that the
corresponding EasyCrypt extractions (`xmss/proofs/extraction/`) faithfully
capture the implemented code.

## Building, Running, and Testing

You can run/test this development either via Docker or natively (if you have the
correct EasyCrypt + Jasmin + solver installation).

### Prerequisites

- Docker approach:  
  - [Docker Engine](https://docs.docker.com/engine/install), installed and running.
- Native approach:  
  - [EasyCrypt (release
  r2026.02)](https://github.com/EasyCrypt/easycrypt/tree/r2026.02), installed
  and configured with Jasmin's EasyCrypt library and the solvers listed below.
  - [Jasmin's compiler (release 2025.06)](https://gitlab.com/jasmin-lang/jasmin-compiler/-/tree/release-2025.06).
  - Alt-Ergo 2.6.0.
  - CVC4 1.8.
  - Z3 4.13.4.

For the native approach, the [EasyCrypt README.md for
r2026.02](https://github.com/EasyCrypt/easycrypt/blob/r2026.02/README.md)
describes installation and solver configuration. More detailed instructions are
provided in the
[INSTALL.md](https://github.com/EasyCrypt/easycrypt/blob/r2026.02/INSTALL.md).

For Jasmin's compiler, it suffices to add its EasyCrypt library (`eclib/`) to
EasyCrypt’s load path under the logical name `Jasmin`. This can be achieved, for
example, by adding the following to the EasyCrypt configuration file:
```config
[general]
idirs = Jasmin:/path/to/jasmin-compiler/eclib
```

### Docker

Run the default verification tests inside the Docker environment:
```shell
make docker-check
```

See the section on the native approach below for details on what the default
verification tests cover.

To explore and interact with the repository inside the container, start an interactive shell:
```shell
make docker-shell
```

This drops you into a shell inside the Docker image with the repository as the
working directory. From there you can run the same commands as in the native
approach (see below).

### Native

Run the default verification tests:
```shell
make check
```

Run a specific verification test `test-x` (defined in `xmss/config/tests.config`):
```shell
make check-x
```

Beyond running tests, these also store test reports in the `xmss/reports/`
directory; this directory is created automatically if it does not exist yet.  

The default verification targets cover all substantive proofs but skip
sanity-checking of setup and environment files. Concretely, they include the
files in `xmss/proofs/correctness/`, `xmss/proofs/specs/`, and
`xmss/proofs/security/`, but not those in `xmss/proofs/common/` and
`xmss/proofs/extraction/`. To verify all components, use `make check-all`; to
verify only the setup and environment files, use `make check-setup`.

Remove EasyCrypt’s cached verification artifacts (`.eco` files),
either across all developments or for an individual one:
```shell
make clean
```

Additionally remove the respective `reports/` directory:
```shell
make clobber
```

### Help with Make

All of the above uses `make` and, hence, goes through this directory's
`Makefile`. To list available targets and brief descriptions:
```shell
make help
```

`make` variables can be overridden (see the `Makefile` in this directory as well
as that in `xmss/`). This allows customization of the setup (e.g., binary paths)
or adjustment of parallelism to speed up verification.

Note, however, that modifying these parameters may affect stability. In
particular, increased parallelism can trigger solver timeouts or related
failures. Unexpected verification failures may therefore occur when deviating
from the default configuration.

