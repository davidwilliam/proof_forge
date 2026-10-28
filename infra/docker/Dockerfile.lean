# Pinned Lean judge/dev image. Linux is required: Comparator's sandbox is bubblewrap.
# The toolchain archive comes from the Lean GitHub release and must match its published
# SHA-256 digest; elan only manages it.
FROM ubuntu:24.04
ARG LEAN_VERSION=4.35.0
ARG LEAN_SHA256_AMD64=7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d
ARG LEAN_SHA256_ARM64=c8f0f8a3920e839718b1343e6781fd80a3e9b1024fbcd7078eb30f54e806b028
ARG TARGETARCH
RUN apt-get update \
 && apt-get install -y --no-install-recommends curl git ca-certificates bubblewrap jq python3 zstd \
 && rm -rf /var/lib/apt/lists/* \
 && mkdir -p /run/user && chmod 755 /run/user   # Comparator's bubblewrap sandbox mounts here
RUN useradd -m -u 1001 forge
USER forge
ENV PATH=/home/forge/.elan/bin:$PATH
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --no-modify-path --default-toolchain none
RUN set -eu; \
    case "${TARGETARCH:-$(dpkg --print-architecture)}" in \
      amd64) asset=lean-${LEAN_VERSION}-linux.tar.zst; sum=${LEAN_SHA256_AMD64} ;; \
      arm64) asset=lean-${LEAN_VERSION}-linux_aarch64.tar.zst; sum=${LEAN_SHA256_ARM64} ;; \
      *) echo "unsupported architecture"; exit 1 ;; \
    esac; \
    curl -sSfL --retry 3 -o /tmp/lean.tar.zst \
      "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/${asset}"; \
    echo "${sum}  /tmp/lean.tar.zst" | sha256sum -c -; \
    dir=/home/forge/.elan/toolchains/leanprover--lean4---v${LEAN_VERSION}; \
    mkdir -p "$dir"; tar --zstd -xf /tmp/lean.tar.zst -C "$dir" --strip-components=1; rm /tmp/lean.tar.zst; \
    elan default leanprover/lean4:v${LEAN_VERSION}; \
    lean --version && lake --version
WORKDIR /work
