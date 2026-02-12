# syntax=docker/dockerfile:1

# Base image: EasyCrypt's release r2026.02
ARG EC_IMAGE=ghcr.io/easycrypt/ec-test-box:r2026.02
FROM ${EC_IMAGE}

# Inherited from base image:
# user (USER): charlie (uid: 1001)
# primary group: root (gid: 0)
# supplementary groups: sudo
# workdir (WORKDIR): /home/charlie

# Create relevant directories and set ownership appropriately
RUN mkdir -p /home/charlie/src /home/charlie/.config/easycrypt /home/charlie/work \
 && chown -R charlie:root /home/charlie/src /home/charlie/work /home/charlie/.config

# Clone Jasmin's compiler repository (release 2025.06)
RUN git clone --branch release-2025.06 --single-branch \
  https://gitlab.com/jasmin-lang/jasmin-compiler.git /home/charlie/src/jasmin-compiler

# Setup EasyCrypt's user configuration to recognize Jasmin's EasyCrypt library
RUN printf '%s\n' \
  '[general]' \
  'idirs = Jasmin:/home/charlie/src/jasmin-compiler/eclib' \
  > /home/charlie/.config/easycrypt/easycrypt.conf \
  && chown charlie:root /home/charlie/.config/easycrypt/easycrypt.conf

# Create and set working directory in image,
# and copy over repository with appropriate permissions
WORKDIR /home/charlie/work
COPY --chown=charlie:root . .

# Entrypoint (prepended to initial command, defaulting to CMD)
ENTRYPOINT ["opam", "exec", "--"]

# Default command to run (appended to entrypoint, defaulting to ENTRYPOINT)
CMD ["make", "check"]
