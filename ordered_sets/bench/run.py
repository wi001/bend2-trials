"""Runs every implementation of spec/ALGORITHM.md and compares them.

Each configuration runs `--reps` times (median reported). Every run's sizes and
sums must equal the C treap's, or the configuration is reported as wrong.
Results are printed and written to bench/results-D<D>.json.

    python3 bench/run.py --D 22 --reps 3
"""
import argparse
import json
import os
import statistics
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def configs(threads):
    bend = ROOT / "bend" / "bench"
    lean = ROOT / "lean" / ".lake" / "build" / "bin"
    out = [
        ("C treap, 1 thread", [ROOT / "c" / "treap"]),
        ("C sorted arrays, 1 thread", [ROOT / "c" / "arrays"]),
        ("C treap, parallel", [ROOT / "c" / "treap_par"]),
    ]
    shared = ROOT / "bend" / "bench_shared"
    for t in threads:
        out.append((f"Bend, {t} thread{'s' if t > 1 else ''}", [bend, "{D}", "+RTS", "--threads", str(t), "-RTS"]))
    for t in threads:
        out.append((f"Bend shared, {t} thread{'s' if t > 1 else ''}", [shared, "{D}", "+RTS", "--threads", str(t), "-RTS"]))
    # the Lean benchmark's second argument is its Task.spawn depth budget; 0 runs on one thread
    out.append(("Lean, 1 thread", [lean / "bench", "{D}", "0"]))
    out.append(("Lean, parallel (Task depth 6)", [lean / "bench", "{D}"]))
    out.append(("Lean fresh, 1 thread", [lean / "bench_fresh", "{D}", "0"]))
    out.append(("Lean fresh, parallel", [lean / "bench_fresh", "{D}"]))
    return out


def parse(text):
    rows = {}
    for line in text.splitlines():
        parts = line.split()
        if not parts:
            continue
        if parts[0] == "build_ms":
            rows["build"] = (float(parts[1]), (int(parts[3]), int(parts[4])))
        elif parts[0] in ("union_ms", "inter_ms", "diff_ms"):
            rows[parts[0][:-3]] = (float(parts[1]), (int(parts[3]), int(parts[5])))
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--D", type=int, default=22)
    ap.add_argument("--reps", type=int, default=3)
    ap.add_argument("--threads", type=int, nargs="*", default=[1, 16])
    args = ap.parse_args()
    env = dict(os.environ, BEND_NO_TELEMETRY="1")
    results, reference = {}, None
    for label, cmd in configs(args.threads):
        if not Path(cmd[0]).exists():
            print(f"skip {label}: {cmd[0]} missing")
            continue
        argv = [str(c).replace("{D}", str(args.D)) for c in cmd]
        if len(argv) == 1:
            argv.append(str(args.D))
        runs = []
        for _ in range(args.reps):
            p = subprocess.run(argv, capture_output=True, text=True, env=env, cwd=Path(argv[0]).parent, timeout=3600)
            runs.append(parse(p.stdout))
        values = {op: statistics.median(r[op][0] for r in runs) for op in ("build", "union", "inter", "diff") if all(op in r for r in runs)}
        answers = {op: runs[0][op][1] for op in values}
        if reference is None:
            reference = answers
        ok = all(r.get(op, (0, None))[1] == reference[op] for r in runs for op in reference)
        results[label] = {"ms": values, "matches_reference": ok, "answers": answers}
        line = "  ".join(f"{op} {values[op]:8.1f} ms" for op in values)
        print(f"{label:28s} {line}  {'ok' if ok else 'WRONG ANSWERS'}")
    out = ROOT / "bench" / f"results-D{args.D}.json"
    out.write_text(json.dumps({"D": args.D, "reps": args.reps, "results": results}, indent=2))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
