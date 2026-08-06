#!/usr/bin/env python3
"""Reproduce Lake's artifact-cache verification race on a CI runner.

Investigating https://github.com/TauCetiProject/TauCeti/issues/2062: roughly a third
of merge-group builds lose the Lake artifact cache entirely and rebuild from scratch,
costing 22 to 28 minutes instead of 3 to 6. The failing runs show one of

    error: no such file or directory (error code: 4294967294)   # -2, ENOENT
    error: <path>.ltar: downloaded artifact hash mismatch, got <other-hash>

on an artifact Lake had just logged as downloaded, and the exception aborts the whole
fetch (Lake/Config/Cache.lean's monitorTransfer verifies with computeFileHash the
instant curl's --write-out JSON reports http_code 200, with no try/catch).

This probe replicates that verification logic exactly: drive curl in parallel mode
with a config file, consume the per-transfer JSON from stderr, and the moment a 200 is
reported, stat and hash the named output file. A local run over 2400 draws saw zero
failures, so the trigger is suspected to be environmental (runner filesystem,
concurrent build I/O, core count). This runs the same test where it actually happens.

Usage:
    cache_fetch_probe.py <hashes-file> <endpoint> <outdir> [--iterations N]

Reports, per iteration, how many verifications hit ENOENT, how many saw a size other
than curl's reported size_download, and how many were clean. Exit status is always 0:
the finding is the report, not the run's success.
"""

import argparse
import hashlib
import json
import os
import subprocess
import sys


def run_once(hashes, endpoint, outdir, tag):
    """One curl -Z batch, verifying each file the instant curl reports it done."""
    os.makedirs(outdir, exist_ok=True)
    for name in os.listdir(outdir):
        os.remove(os.path.join(outdir, name))

    cfg = os.path.join(outdir, os.pardir, f"curl-{tag}.cfg")
    with open(cfg, "w") as fh:
        for h in hashes:
            fh.write(f'url = "{endpoint}/{h}.art"\n')
            fh.write(f'-o "{os.path.join(outdir, h + ".ltar")}"\n')

    # Mirrors Lake's own invocation: -Z (parallel), --retry 3, JSON to stderr.
    proc = subprocess.Popen(
        ["curl", "-Z", "-X", "GET", "-L", "--retry", "3",
         "-s", "-w", "%{stderr}%{json}\n", "--config", cfg],
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1)

    enoent, short, clean, non200, unparsed = [], [], 0, 0, 0
    for line in proc.stderr:
        line = line.strip()
        if not line:
            continue
        try:
            rec = json.loads(line)
        except json.JSONDecodeError:
            unparsed += 1
            continue
        if rec.get("http_code") not in (200, 201):
            non200 += 1
            continue
        path = rec.get("filename_effective") or ""
        want = rec.get("size_download", -1)
        # This is the moment Lake calls computeFileHash. Do exactly that.
        try:
            with open(path, "rb") as fh:
                data = fh.read()
        except FileNotFoundError:
            enoent.append(os.path.basename(path))
            continue
        if len(data) != want:
            short.append((os.path.basename(path), len(data), want))
        else:
            clean += 1
            hashlib.sha256(data).digest()   # same read-and-hash cost as Lake

    proc.wait()
    proc.stdout.read()
    return {"clean": clean, "enoent": enoent, "short": short,
            "non200": non200, "unparsed": unparsed, "rc": proc.returncode}


def main(argv):
    ap = argparse.ArgumentParser()
    ap.add_argument("hashes")
    ap.add_argument("endpoint")
    ap.add_argument("outdir")
    ap.add_argument("--iterations", type=int, default=1)
    args = ap.parse_args(argv[1:])

    with open(args.hashes) as fh:
        hashes = [l.strip() for l in fh if l.strip()]
    print(f"probing {len(hashes)} artifacts x {args.iterations} iteration(s) "
          f"= {len(hashes) * args.iterations} verifications", flush=True)

    tot_enoent = tot_short = tot_clean = 0
    for i in range(1, args.iterations + 1):
        r = run_once(hashes, args.endpoint, args.outdir, i)
        tot_enoent += len(r["enoent"])
        tot_short += len(r["short"])
        tot_clean += r["clean"]
        print(f"  iter {i}: clean={r['clean']} enoent={len(r['enoent'])} "
              f"short={len(r['short'])} non200={r['non200']} "
              f"unparsed={r['unparsed']} curl_rc={r['rc']}", flush=True)
        for name in r["enoent"]:
            print(f"    ENOENT {name}", flush=True)
        for name, got, want in r["short"]:
            print(f"    SHORT  {name} on-disk={got} curl-reported={want}", flush=True)

    total = tot_clean + tot_enoent + tot_short
    print(f"\nTOTAL verifications={total} clean={tot_clean} "
          f"enoent={tot_enoent} short={tot_short}")
    if tot_enoent or tot_short:
        print("REPRODUCED: curl reported a completed 200 for a file that was absent "
              "or short at verification time.")
    else:
        print("NOT REPRODUCED in this configuration.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
