"""Fetch the pinned Muse Glimmer snapshots into the Modal volume that glimmer_vllm.py mounts,
on a CPU container, so GPU containers start from the volume instead of the network.

Run once:  modal run infra/modal/glimmer_download.py
The repositories and revisions must equal those in glimmer_vllm.py.
"""
import modal

SNAPSHOTS = [("meta-models/Muse-Glimmer-30B", "cec94fcfd6512f2cfe708138c32533b346ea4f69"),
             ("meta-models/Muse-Glimmer-30B-assistant", "c676cce91658f9568aaf264a416211e2782735b7")]

image = (modal.Image.debian_slim(python_version="3.12")
         .uv_pip_install("huggingface_hub==2.3.0")
         .env({"HF_XET_HIGH_PERFORMANCE": "1", "HF_HUB_DISABLE_TELEMETRY": "1"}))
hf_cache = modal.Volume.from_name("proofforge-hf-cache", create_if_missing=True)
app = modal.App("proofforge-glimmer-download")


@app.function(image=image, volumes={"/root/.cache/huggingface": hf_cache}, cpu=4, memory=8192, timeout=3600)
def download():
    from huggingface_hub import snapshot_download
    for repo, rev in SNAPSHOTS:
        print(repo, rev, snapshot_download(repo, revision=rev))
    hf_cache.commit()
