# Pinned Lean judge/dev image. Linux is required: Comparator's sandbox is bubblewrap.
# The base image is pinned by its multi-platform digest (ubuntu:24.04 as of 2026-10-28), the
# elan binary by release and SHA-256, and the toolchain archive comes from the Lean GitHub
# release and must match its published SHA-256 digest; elan only manages it. The apt packages
# come from the Ubuntu archive at build time.
FROM ubuntu:24.04@sha256:24737cef17f4e22b1977df7d9a05e77c4e28b7da5b8911f8d8ccda136bf3573c
ARG LEAN_VERSION=4.35.0
ARG LEAN_SHA256_AMD64=7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d
ARG LEAN_SHA256_ARM64=c8f0f8a3920e839718b1343e6781fd80a3e9b1024fbcd7078eb30f54e806b028
ARG ELAN_VERSION=4.2.4
ARG ELAN_SHA256_AMD64=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
ARG ELAN_SHA256_ARM64=05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9
ARG TARGETARCH
RUN apt-get update \
 && apt-get install -y --no-install-recommends curl git ca-certificates bubblewrap jq python3 zstd \
 && rm -rf /var/lib/apt/lists/* \
 && mkdir -p /run/user && chmod 755 /run/user   # Comparator's bubblewrap sandbox mounts here
RUN useradd -m -u 1001 forge
USER forge
ENV PATH=/home/forge/.elan/bin:$PATH
RUN set -eu; \
    case "${TARGETARCH:-$(dpkg --print-architecture)}" in \
      amd64) asset=elan-x86_64-unknown-linux-gnu.tar.gz; sum=${ELAN_SHA256_AMD64} ;; \
      arm64) asset=elan-aarch64-unknown-linux-gnu.tar.gz; sum=${ELAN_SHA256_ARM64} ;; \
      *) echo "unsupported architecture"; exit 1 ;; \
    esac; \
    curl -sSfL --retry 3 -o /tmp/elan.tar.gz \
      "https://github.com/leanprover/elan/releases/download/v${ELAN_VERSION}/${asset}"; \
    echo "${sum}  /tmp/elan.tar.gz" | sha256sum -c -; \
    tar -xzf /tmp/elan.tar.gz -C /tmp; \
    /tmp/elan-init -y --no-modify-path --default-toolchain none; rm /tmp/elan.tar.gz /tmp/elan-init
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
