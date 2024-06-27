# syntax=docker/dockerfile:1

# We use Nix for the build.
FROM nixos/nix:2.22.0 AS builder

# Create and navigate to a working directory
WORKDIR /home/user

# Copy all of the source code into the working directory. Impurities like
# additional files and previous build results will be filtered by Nix. Note that
# all files which are considered *tracked* by Git will be used for the build,
# even if they are modified.
COPY . .

# Patch Windows line endings if the repository was cloned on Windows.
RUN nix-shell -p dos2unix --run 'find . -exec dos2unix {} +'

# Verify all proofs and build the demo.
RUN nix-build

# Copy the demo with all runtime dependencies (ignoring build-time dependencies)
# to a separate folder. Such a subset of the Nix store is called a closure and
# enables us to create a minimal Docker container.
RUN mkdir closure
RUN nix-store -qR result | xargs cp -Rt closure

# Start building the final container.
FROM scratch

# Copy the demo (it's runtime closure) to the final container.
COPY --from=builder /home/user/closure /nix/store

# Copy the symlink to the demo derivation, mostly for convenience.
COPY --from=builder /home/user/result /demo

# Enforce a UTF-8 locale to ensure that the Haskell runtime can output all the
# Unicode characters.
ENV LC_ALL=C.UTF-8

CMD ["/demo/bin/EPVL"]
