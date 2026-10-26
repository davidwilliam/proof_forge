# Pinned Lean judge/dev image. Linux is required: Comparator's sandbox is bubblewrap.
FROM ubuntu:24.04
ARG LEAN_TOOLCHAIN=leanprover/lean4:v4.35.0
RUN apt-get update \
 && apt-get install -y --no-install-recommends curl git ca-certificates bubblewrap jq python3 \
 && rm -rf /var/lib/apt/lists/* \
 && mkdir -p /run/user && chmod 755 /run/user   # Comparator's bubblewrap sandbox mounts here
RUN useradd -m -u 1001 forge
USER forge
ENV PATH=/home/forge/.elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --no-modify-path --default-toolchain ${LEAN_TOOLCHAIN} \
 && lean --version && lake --version
WORKDIR /work
