"""Level 1: Certified (scorecard/SPEC.md, "Level 1"). `scorecard certify --repo R --commit C [--manifest vbm-proof.toml] [--sandbox LAUNCHER] [--out FILE]` runs NO code of the candidate: it reads a proof manifest and the files it declares as DATA,
through the runner's one file guard. The runner module is passed in (`rt`: its Reject, git, safe_read, open_subject), so there is one guard and one clone path for both levels."""
import hashlib, json, shutil, sys

import scorecard_export, scorecard_manifest

SCHEMA_VERSION = "scorecard-2"


def metric(mid, dim, status, value=None, reason=None, source="scorer-computed", **extra):
    """One Level 1 metric record. `source` is scorer-computed or self-reported (SPEC, number hygiene); a self-reported record is informational and never judged."""
    assert source in ("scorer-computed", "self-reported") and (source == "scorer-computed" or status == "info")
    m = {"id": mid, "dimension": dim, "level": 1, "source": source, "status": status, "value": value}
    if reason: m["reason"] = reason
    return {**m, **extra}


def read_export(ctx, manifest, rt):
    """Intake of the declared export (SPEC Level 1, step 2). Returns (Export or None, the export's card block, metrics). The candidate chose its bytes: an unreadable, mis-hashed or hostile export FAILS."""
    path, declared = manifest["export"]["path"], manifest["export"]["sha256"]
    raw = rt.safe_read(ctx, path, cap=scorecard_export.MAX_BYTES)
    block = {"path": path}
    if raw is None: return None, block, [metric("verified.export_intake", "verified", "fail", reason=f"the declared export cannot be read: {'; '.join(sorted(ctx['skipped']))}")]
    block.update(sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw))
    if block["sha256"] != declared: return None, block, [metric("verified.export_intake", "verified", "fail", reason=f"the export's sha256 {block['sha256']} is not the {declared} the manifest declares: the manifest is stale or the file was swapped")]
    try:
        with scorecard_export.bounded():
            X = scorecard_export.intake(raw)
    except scorecard_export.ExportError as e: return None, block, [metric("verified.export_intake", "verified", "fail", reason=str(e))]
    kinds = {}
    for d in X.decls.values(): kinds[d["kind"]] = kinds.get(d["kind"], 0) + 1
    block.update(X.counts, declarations=len(X.decls), declaration_kinds=dict(sorted(kinds.items())))
    return X, block, [metric("verified.export_intake", "verified", "pass", value=True), metric("verified.export_meta", "verified", "info", value=X.meta, source="self-reported", reason="what the exporter wrote about itself: shown, never judged")]


def run(a, rt):
    repo, commit, launcher, scratch, wt = rt.open_subject(a)
    try:
        ctx = dict(wt=wt, commit=commit, scratch=scratch, sandbox=launcher, skipped=set())
        raw = rt.safe_read(ctx, a.manifest)
        if raw is None: raise rt.Reject(f"no manifest: {commit[:12]} has no readable {a.manifest} ({'; '.join(sorted(ctx['skipped']))})")
        try: manifest = scorecard_manifest.load(raw.decode())
        except (scorecard_manifest.ManifestError, UnicodeDecodeError) as e: raise rt.Reject(str(e))
        X, export_block, metrics = read_export(ctx, manifest, rt)
        sc_sha = rt.git(rt.HERE, "rev-parse", "HEAD", check=False).strip() or None
        card = {"schema": SCHEMA_VERSION, "level": 1, "scorecard": {"sha": sc_sha},
                "subject": {"commit": commit, "commit_date": rt.git(repo, "log", "-1", "--format=%cI", commit).strip()},
                "manifest": {"path": a.manifest, "sha256": hashlib.sha256(raw).hexdigest()}, "export": export_block, "metrics": metrics, "skipped_files": sorted(ctx["skipped"])}
    finally:
        if a.keep: print(f"scorecard: scratch kept at {scratch}", file=sys.stderr)
        else: shutil.rmtree(scratch, ignore_errors=True)
    out = json.dumps(card, indent=2) + "\n"
    if a.out: open(a.out, "w").write(out)
    else: sys.stdout.write(out)
    return 0
