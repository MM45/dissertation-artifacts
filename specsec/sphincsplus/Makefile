# -*- Makefile -*-

# Environment/Setup
## EasyCrypt
EC_BIN ?= easycrypt
EC_PROOFS_ROOT ?= proofs

### Runtest
EC_RUNTEST_ENV ?=
EC_RUNTEST_FILE ?= config/tests.config
EC_RUNTEST_JOBS ?= 1
EC_RUNTEST_REPORT_DIR ?= reports

EC_RUNTEST_OPTS = -jobs $(EC_RUNTEST_JOBS)
EC_RUNTEST = $(strip $(EC_RUNTEST_ENV) $(EC_BIN) runtest $(EC_RUNTEST_OPTS) $(EC_RUNTEST_FILE))

## Special
.DEFAULT_GOAL := check


# Targets
## EasyCrypt
check: check-default

check-%: FORCE
	@echo "Creating $(EC_RUNTEST_REPORT_DIR) directory if it does not exist yet..."
	@mkdir -p "$(EC_RUNTEST_REPORT_DIR)"
	@echo "Starting test $*..."
	$(EC_RUNTEST) -report "$(EC_RUNTEST_REPORT_DIR)/$*.log" $*

clean:
	@echo "Removing EasyCrypt's cached verification results ('.eco' files)..."
	@if [ -d "$(EC_PROOFS_ROOT)" ]; then \
		find "$(EC_PROOFS_ROOT)" -type f -name '*.eco' -exec rm -f '{}' + ; \
	fi

dry-clean:
	@echo "make clean would remove the following files..."
	@if [ -d "$(EC_PROOFS_ROOT)" ]; then \
		find "$(EC_PROOFS_ROOT)" -type f -name '*.eco' -print ; \
	fi

clobber: clean
	@echo "Removing $(EC_RUNTEST_REPORT_DIR) directory..."
	@rm -rf "$(EC_RUNTEST_REPORT_DIR)"

FORCE:

## Help
help:
	@printf "\n"
	@printf "Usage:\n"
	@printf "The primary entry point is the Makefile in the parent directory (specsec/).\n"
	@printf "Run 'make help' there for available targets and documentation.\n\n"

## Special
.PHONY: check clean dry-clean clobber FORCE
.PHONY: help
