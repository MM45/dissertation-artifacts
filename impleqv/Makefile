# -*- Makefile -*-

# Environment/Setup
## Developments
XMSS_DIR ?= xmss

## Docker
DOCKER_BIN ?= docker
DOCKER_IMAGE ?= diss-art-impleqv:r2026.02
DOCKER_TTY ?= -t

## Special
.DEFAULT_GOAL := check

# Targets
## Docker
docker-check: docker-run
docker-check-xmss: docker-run-xmss

docker-safe:
	@if [ -f /.dockerenv ]; then \
		echo "Error: Docker target invoked inside a (Docker) container."; \
		exit 2; \
	fi
	@$(DOCKER_BIN) info >/dev/null 2>&1 || { \
		echo "Error: Docker daemon unresponsive. Ensure it is running and you have the appropriate permissions."; \
		exit 2; \
	}

docker-build: docker-safe
	$(DOCKER_BIN) build -t $(DOCKER_IMAGE) .

docker-run: docker-build
	$(DOCKER_BIN) run --rm $(DOCKER_TTY) $(DOCKER_IMAGE)

docker-run-xmss: docker-build
	$(DOCKER_BIN) run --rm $(DOCKER_TTY) $(DOCKER_IMAGE) make check-xmss

docker-shell: docker-build
	$(DOCKER_BIN) run --rm -it $(DOCKER_IMAGE) bash


## EasyCrypt
check: check-xmss
check-xmss: check-xmss-default

check-%: check-xmss-% ; @:

check-xmss-%: FORCE
	@echo "Entering $(XMSS_DIR) directory to check $*..."
	@$(MAKE) -C $(XMSS_DIR) check-$*

clean: clean-xmss

clean-xmss:
	@echo "Entering $(XMSS_DIR) directory to clean..."
	@$(MAKE) -C $(XMSS_DIR) clean

dry-clean: dry-clean-xmss

dry-clean-xmss:
	@echo "Entering $(XMSS_DIR) directory to dryrun clean..."
	@$(MAKE) -C $(XMSS_DIR) dry-clean

clobber: clobber-xmss

clobber-xmss:
	@echo "Entering $(XMSS_DIR) directory to clobber..."
	@$(MAKE) -C $(XMSS_DIR) clobber

FORCE:

## Help
help:
	@printf "\n"
	@printf "Usage:\n"
	@printf "  make <target>\n\n"

	@printf "Main targets:\n"
	@printf "  %-18s %s\n"   "docker-check"      "Run default EasyCrypt tests in Docker."
	@printf "  %-18s %s\n"   "check"             "Run default EasyCrypt tests."
	@printf "  %-18s %s\n"   "clean"             "Remove EasyCrypt's cached verification results (*.eco files)."

	@printf "Miscellaneous targets:\n"
	@printf "  %-18s %s\n" "docker-safe"       "Check if it is safe to run Docker targets."
	@printf "  %-18s %s\n" "docker-build"      "Build Docker image ($(DOCKER_IMAGE))."
	@printf "  %-18s %s\n" "docker-run"        "Run Docker image ($(DOCKER_IMAGE)), equivalent to 'docker-check'."
	@printf "  %-18s %s\n" "docker-shell"      "Start an interactive shell in Docker (instead of running tests)."
	@printf "  %-18s %s\n" "check-<name>"      "Run a specific EasyCrypt test."
	@printf "  %-18s %s\n" "dry-clean"         "Show what 'make clean' would remove."
	@printf "  %-18s %s\n" "clobber"           "clean + remove report directory."

## Special
.PHONY: \
  docker-check docker-check-xmss \
  docker-safe docker-build docker-run docker-run-xmss docker-shell
.PHONY: \
  check check-xmss \
  clean clean-xmss\
  dry-clean dry-clean-xmss \
  clobber clobber-xmss \
  FORCE
.PHONY: help
