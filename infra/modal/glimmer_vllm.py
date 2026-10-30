"""Muse Glimmer 30B behind an OpenAI-compatible Chat Completions endpoint on Modal (vLLM).

One H100 80GB, BF16 weights, native ATEM tool calls through vLLM's `muse_glimmer` tool and
reasoning parsers, DFlash speculative decoding with the drafter Meta ships for the model.
Requests must carry `Authorization: Bearer <key>`; the key lives in the Modal secret
`glimmer-api-key` as VLLM_API_KEY and is read by vLLM from the environment, never passed
on a command line. The server scales to zero after SCALEDOWN_S idle seconds and never runs
more than one container.

Deploy:  modal deploy infra/modal/glimmer_vllm.py
Stop:    modal app stop proofforge-glimmer
See infra/modal/README.md.
"""
import json
import subprocess

import modal

MODEL = "meta-models/Muse-Glimmer-30B"
MODEL_REVISION = "cec94fcfd6512f2cfe708138c32533b346ea4f69"
DRAFT = "meta-models/Muse-Glimmer-30B-assistant"
DRAFT_REVISION = "c676cce91658f9568aaf264a416211e2782735b7"
SERVED_NAME = "glimmer/muse-glimmer-30b"   # the routed id in agents/meta_client.py
SPECULATIVE = True                         # DFlash drafter; False serves the target model alone
DRAFT_TOKENS = 15                          # drafter block of 16: one bonus position plus 15 drafts
MAX_MODEL_LEN = 131072
MAX_NUM_SEQS = 8
PORT = 8000
SCALEDOWN_S = 20 * 60
GPU = "H100"
CPU_CORES = 4
MEMORY_MIB = 32 * 1024

# Official vLLM 0.32.0 image (x86_64, CUDA 13.0, torch 2.13.0), pinned by digest.
VLLM_IMAGE = "vllm/vllm-openai:v0.32.0-x86_64@sha256:6ee133356d49ed24cee03dd0cda3d3980279a11c107ce3e752c89e76540f41c9"

image = (
    modal.Image.from_registry(VLLM_IMAGE)
    .entrypoint([])
    .run_commands("ln -sf \"$(command -v python3)\" /usr/local/bin/python && python --version")
    .env({"HF_XET_HIGH_PERFORMANCE": "1", "VLLM_LOG_STATS_INTERVAL": "30",
          "HF_HUB_DISABLE_TELEMETRY": "1", "VLLM_NO_USAGE_STATS": "1", "DO_NOT_TRACK": "1"})
)
hf_cache = modal.Volume.from_name("proofforge-hf-cache", create_if_missing=True)
vllm_cache = modal.Volume.from_name("proofforge-vllm-cache", create_if_missing=True)

app = modal.App("proofforge-glimmer")


def serve_command():
    cmd = ["vllm", "serve", MODEL, "--revision", MODEL_REVISION,
           "--served-model-name", SERVED_NAME,
           "--host", "0.0.0.0", "--port", str(PORT),
           "--dtype", "bfloat16",
           "--max-model-len", str(MAX_MODEL_LEN),
           "--max-num-seqs", str(MAX_NUM_SEQS),
           "--gpu-memory-utilization", "0.92",
           "--limit-mm-per-prompt", json.dumps({"image": 0, "video": 0}),
           "--enable-prefix-caching",
           "--enable-prompt-tokens-details",
           "--enable-auto-tool-choice",
           "--tool-call-parser", "muse_glimmer",
           "--reasoning-parser", "muse_glimmer",
           "--generation-config", "auto",
           "--disable-uvicorn-access-log"]
    if SPECULATIVE:
        cmd += ["--speculative-config", json.dumps(
            {"method": "dflash", "model": DRAFT, "revision": DRAFT_REVISION,
             "num_speculative_tokens": DRAFT_TOKENS})]
    return cmd


@app.server(
    image=image,
    gpu=GPU,
    cpu=CPU_CORES,
    memory=MEMORY_MIB,
    secrets=[modal.Secret.from_name("glimmer-api-key")],
    volumes={"/root/.cache/huggingface": hf_cache, "/root/.cache/vllm": vllm_cache},
    port=PORT,
    unauthenticated=True,          # the Modal proxy is open; vLLM enforces the bearer key
    min_containers=0,
    max_containers=1,
    scaledown_window=SCALEDOWN_S,
    startup_timeout=40 * 60,       # weight load from the volume plus compilation and CUDA graphs
    exit_grace_period=60,
)
class Glimmer:
    @modal.enter()
    def start(self):
        cmd = serve_command()
        print(*cmd)
        self.proc = subprocess.Popen(cmd)

    @modal.exit()
    def stop(self):
        self.proc.terminate()
