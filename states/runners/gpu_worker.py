#!/usr/bin/env python3
"""GPU 车道 worker：把作业卡的 prompt + 输入文件发给本地 OpenAI 兼容端点。

环境变量（必填）：GPU_API_BASE（如 http://127.0.0.1:11434/v1）、GPU_MODEL；
可选：GPU_API_KEY。端点须实现 POST {base}/chat/completions。

作业卡字段：id, prompt（prompt.md 路径，相对仓库根）, input（目录，其下文本文件并入上下文），
output（result.json 路径，相对仓库根）。模型须输出合法 JSON，原样落盘。

用法：python states/runners/gpu_worker.py [--once]
（换一个推理引擎 = 只改本文件的 call_model 函数）
"""

import json
import os
import time
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
Q = ROOT / "states/queue/gpu"
API_BASE = os.environ.get("GPU_API_BASE", "")
API_KEY = os.environ.get("GPU_API_KEY", "sk-local")
MODEL = os.environ.get("GPU_MODEL", "")


def stamp(card: dict, status: str, log: str = "") -> None:
    card["status"] = status
    card["updated"] = datetime.now(timezone.utc).isoformat()
    dest = Q / status / f"{card['id']}.json"
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(card, ensure_ascii=False, indent=1), encoding="utf-8")
    if log:
        (Q / status / card["id"]).mkdir(parents=True, exist_ok=True)
        (Q / status / card["id"] / "log.txt").write_text(log, encoding="utf-8")
    old = Q / "pending" / f"{card['id']}.json"
    if old.exists() and status != "pending":
        old.unlink()


def call_model(prompt: str) -> str:
    req = urllib.request.Request(
        f"{API_BASE}/chat/completions",
        data=json.dumps({
            "model": MODEL,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0.2,
        }).encode("utf-8"),
        headers={"Content-Type": "application/json", "Authorization": f"Bearer {API_KEY}"},
    )
    with urllib.request.urlopen(req, timeout=1800) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    return data["choices"][0]["message"]["content"]


def run_once() -> int:
    if not API_BASE or not MODEL:
        print("GPU_API_BASE/GPU_MODEL 未配置，跳过 GPU 车道。")
        return 0
    for cp in sorted((Q / "pending").glob("*.json")):
        card = json.loads(cp.read_text(encoding="utf-8"))
        stamp(card, "running")
        try:
            prompt = (ROOT / card["prompt"]).read_text(encoding="utf-8")
            for f in sorted((ROOT / card.get("input", card["id"] + "/in")).glob("*")):
                if f.is_file():
                    prompt += f"\n\n--- {f.name} ---\n" + f.read_text(encoding="utf-8", errors="ignore")
            raw = call_model(prompt)
            start = raw.find("{"); end = raw.rfind("}")
            parsed = json.loads(raw[start:end + 1]) if start != -1 else {"raw": raw}
            out = ROOT / card["output"]
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(json.dumps(parsed, ensure_ascii=False, indent=1), encoding="utf-8")
            stamp(card, "done")
        except Exception as e:  # noqa: BLE001
            stamp(card, "failed", repr(e))
    return 0


def main() -> None:
    if "--once" in sys.argv:
        run_once()
        return
    while True:
        run_once()
        time.sleep(60)


if __name__ == "__main__":
    main()
