# This image allows us to bake in our opam deps, shaving ~12 minutes off of each build.
# pinned 9.0 tag
FROM rocq/rocq-prover@sha256:787ea5569c9bf40e03a2255224365cb2fb0ae4a446fc60565dd61b1656d1699d

# HACK: until https://github.com/rocq-community/docker-rocq/issues/32 is resolved,
# change the dune pin to a 3.23.1; this inflates our image size a bit since the
# base still bakes in the older version.
USER rocq
RUN opam pin remove -y dune \
 && opam update -y \
 && opam install -y -j 4 dune.3.23.1

# since we remove the pin, there is no harm if this image is out of date--other than
# longer build time.
COPY --chown=rocq:rocq iris-richwasm.opam /tmp/iris-richwasm/iris-richwasm.opam
RUN opam pin add -y -n -k path iris-richwasm /tmp/iris-richwasm \
 && opam install -y --deps-only --confirm-level=unsafe-yes -j 4 iris-richwasm \
 && opam pin remove -y iris-richwasm \
 && rm -rf /tmp/iris-richwasm \
 && opam clean -a

USER root
RUN apt-get update -y -q \
 && apt-get install -y --no-install-recommends wabt \
 && rm -rf /var/lib/apt/lists/*

# This is GitHub specific, since actions override $HOME and bypass the image entrypoint
ENV OPAMROOT=/home/rocq/.opam
ENV OPAMROOTISOK=1

USER rocq
