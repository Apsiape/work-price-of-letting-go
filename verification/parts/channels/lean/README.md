# Lean proof package

## Reproduce

Install the exact toolchain named in `lean-toolchain` (leanprover/lean4:v4.30.0). From `verification/parts/channels/lean/`, run:

```sh
lake exe cache get
lake build
```

The cache command obtains the pinned Git dependencies and their standard Mathlib build cache. Plain `lake build` compiles the default Lean library from the shipped sources. The generated `lake-manifest.json` fixes all dependency revisions; ordinary reproduction does not require `lake update`.

Set `LEAN_NUM_THREADS=1` and allow at least 8 GiB of available physical memory. Run one Lean compiler process on the machine at a time, using an external process lock when needed. The clean test uses `-j1 -M6144` through its external compiler launcher; existing package options are preserved.

Historical Python replays and other verification records, where supplied, remain optional additional checks. Plain `lake build` does not run a statement comparator or independent kernel replay.
