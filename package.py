# type: ignore
import os


req(
    "7zip",
    "minio",
    "requests",
)

ava("python")

src_path = os.path.join(this.root, "src")
env("PYTHONPATH").insert(src_path)
env("PATH").insert(src_path)
