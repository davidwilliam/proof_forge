# Muse Glimmer 30B on Modal

`glimmer_vllm.py` serves Meta's open-weight Muse Glimmer 30B (Apache 2.0) as an OpenAI-compatible Chat Completions endpoint with native tool calls. The agents reach it through the routed model id `glimmer/muse-glimmer-30b` (`agents/meta_client.py`).

| Item | Value |
|---|---|
| GPU | 1 x H100 80GB (Modal `gpu="H100"`), 4 CPU cores, 32 GiB memory requested |
| Engine | vLLM 0.32.0, official image `vllm/vllm-openai:v0.32.0-x86_64` pinned by digest (CUDA 13.0, torch 2.13.0) |
| Model | `meta-models/Muse-Glimmer-30B` at revision `cec94fcfd6512f2cfe708138c32533b346ea4f69`, BF16, the repository's own chat template |
| Drafter | `meta-models/Muse-Glimmer-30B-assistant` at revision `c676cce91658f9568aaf264a416211e2782735b7`, DFlash speculative decoding, 15 draft tokens |
| Tool calls | `--enable-auto-tool-choice --tool-call-parser muse_glimmer --reasoning-parser muse_glimmer` (the model writes ATEM `<atem:invoke>` blocks; vLLM returns them as OpenAI `tool_calls` and the reasoning channel as `reasoning_content`) |
| Context | 131,072 tokens, up to 8 concurrent sequences, prefix caching on, cached prompt tokens reported in `usage.prompt_tokens_details` |
| Sampling | the model's `generation_config.json` (temperature 1.0, top_p 0.95, top_k 64) |
| Images | disabled (`--limit-mm-per-prompt` 0 images, 0 videos) |
| Scaling | 0 to 1 container (`max_containers=1`), scales to zero after 20 idle minutes |
| Auth | every `/v1` request needs `Authorization: Bearer <key>`; the key is the Modal secret `glimmer-api-key` (`VLLM_API_KEY`), read by vLLM from the environment |

The Modal proxy itself is unauthenticated; vLLM rejects `/v1` requests without the key with HTTP 401. `/health` is open. A Modal Server has no request queue: while no container is up, requests get HTTP 503 and the first one starts a container, which takes several minutes. Warm it before a run by polling `/health` until it returns 200.

## Status

Not yet started on a GPU: Modal refuses every GPU type (H100, A100-80GB, L40S, A10G, T4) on this workspace with "Please add a payment method to use ... GPU functions". The image builds and the CPU download runs. The behavior described above is the configuration, not a measured result, until the first deploy.

## Deploy

```
modal run infra/modal/glimmer_download.py   # once, CPU only: both snapshots into the volume proofforge-hf-cache
modal deploy infra/modal/glimmer_vllm.py
```

Then put the base URL in `.env` as `GLIMMER_API_BASE=https://<workspace>--proofforge-glimmer-glimmer.us-east.modal.direct/v1` (printed by `modal deploy`) next to `GLIMMER_API_KEY`, which must equal the secret's `VLLM_API_KEY`.

Check it: `python3 agents/smoke_test.py glimmer/muse-glimmer-30b`.

## Stop

```
modal app stop proofforge-glimmer
```

Stopping the app ends the container and the deployment; `modal deploy` brings it back. Without a stop the container still scales to zero after 20 idle minutes.

## Price

Self-hosted serving has no per-token list price. `infra/modal/bench_glimmer.py` measures prefill and decode throughput on A0-shaped dev-task requests at concurrency 1 and 2. The per-token price for `agents/budget.py` is the container's Modal price per second (H100 $0.001097/s, plus 4 cores at $0.0000131/core/s and 32 GiB at $0.00000222/GiB/s, $0.00122044/s in all, Modal pricing page 2026-10-29) divided by the measured throughput: output tokens at the aggregate decode rate at concurrency 2 (E1 runs with `--parallel 2`), uncached input tokens at the prefill rate. `agents/budget.py` has no Glimmer entry until that measurement exists, so a budgeted run with the Glimmer id fails at its first call instead of running at an invented price.
