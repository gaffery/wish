# type: ignore
import os


req(
    "7zip",
    "python",
    "python-sat",
    "requests",
    "minio",
)

ava("python")

src_path = os.path.join(this.root, "src")
env("PYTHONPATH").insert(src_path)
env("PATH").insert(src_path)
