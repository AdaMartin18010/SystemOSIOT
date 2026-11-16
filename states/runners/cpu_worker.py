#!/usr/bin/env python3
"""CPU 车道 worker：轮询 states/queue/cpu/pending/，执行作业卡。

作业卡字段：id, command（在仓库根执行的 shell 命令）, acceptance（可选，done 前执行），
output（可选，期望产物路径）。结果写回卡内 status: done|failed，并写 out/log.txt。

用法：python states/runners/cpu_worker.py [--once]
"""

import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
Q = ROOT / "states/queue/cpu"


def stamp(card: dict, status: str, log: str = "") -> None:
    card["status"] = status
    card["updated"] = datetime.now(timezone.utc).isoformat()
    card_path = Q / status / f"{card['id']}.json"
    card_path.parent.mkdir(parents=True, exist_ok=True)
    card_path.write_text(json.dumps(card, ensure_ascii=False, indent=1), encoding="utf-8")
    if log:
        (card_path.parent / card["id"] / "log.txt").parent.mkdir(parents=True, exist_ok=True)
        (Q / status / card["id"] / "log.txt").write_text(log, encoding="utf-8")
    old = Q / "pending" / f"{card['id']}.json"
    if old.exists() and status != "pending":
        old.unlink()


def run_once() -> int:
    cards = sorted((Q / "pending").glob("*.json"))
    for cp in cards:
        card = json.loads(cp.read_text(encoding="utf-8"))
        stamp(card, "running")
        log = f"$ {card['command']}\n"
        try:
            r = subprocess.run(card["command"], shell=True, cwd=ROOT,
                               capture_output=True, text=True, timeout=card.get("timeout", 1800))
            log += r.stdout + r.stderr
            if r.returncode != 0:
                stamp(card, "failed", log + f"\nexit={r.returncode}")
                continue
            if card.get("acceptance"):
                a = subprocess.run(card["acceptance"], shell=True, cwd=ROOT,
                                   capture_output=True, text=True)
                log += f"\n$ {card['acceptance']}\n" + a.stdout + a.stderr
                if a.returncode != 0:
                    stamp(card, "failed", log + f"\nacceptance_exit={a.returncode}")
                    continue
            stamp(card, "done", log)
        except subprocess.TimeoutExpired:
            stamp(card, "failed", log + "\nTIMEOUT")
    return len(cards)


def main() -> None:
    if "--once" in sys.argv:
        sys.exit(0 if run_once() >= 0 else 1)
    while True:
        run_once()
        time.sleep(30)


if __name__ == "__main__":
    main()
