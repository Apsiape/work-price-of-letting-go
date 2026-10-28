#!/usr/bin/env python3
"""verify.py -- run every machine check of the paper and print a scorecard.

    python3 verify.py                 # run all Python checks (about 15 minutes), write SCORECARD.md
    python3 verify.py --quick         # the checks that finish in under a minute each (about 3 minutes)
    python3 verify.py --negative      # run the negative controls: each must FAIL with a diagnostic
    python3 verify.py --lean          # also compile the Lean proofs (needs Lean 4 and Mathlib, see README)
    python3 verify.py --select law    # run only checks whose path contains the string; results accumulate in results.json
    python3 verify.py --report        # write SCORECARD.md from results.json without running anything

Exit status 0 means every selected check passed (or, with --negative, that every corruption was caught).
A referee does not need to read the scripts to use this file: the scorecard has one row per script, naming the
claim it checks, the script, the part of the paper and the result; Table 7 of the paper (Verification status) names
the scripts against the statements they support.
"""
import subprocess, sys, time, pathlib, os, json

HERE = pathlib.Path(__file__).resolve().parent
ARGS = set(sys.argv[1:])

# (claim as stated in the paper, relative script path, approximate seconds, part of the paper)
CHECKS = [
    ("Whole-block identity on random energy-conserving devices, one step and two-visit schedules with an adaptive observer; global purity with a mixed device and its purifier (Lemma 3.4)", "checks/check_identity.py", 5, "Section 3"),
    ("Protocol numbers, record-export, joint-record and blank-randomization examples, timing of Jun et al., the graded-control curve h2(eta), the held-arm camera frame, the endpoint rule, confidence endpoints, fresh probes, the per-stroke variance assumption and the flipped loan (Section 10); heat-form numbers of the certificate with randomized settings (Prop. 9.1(d)); m = 0.197 of Figure 3; the Gibbs-qubit reset of Section 5; embezzling trace distance sqrt(2/n) (Section 2)", "checks/check_protocol_numbers.py", 5, "Sections 2, 5, 9, 10"),
    ("Fiber law: constant-answer erasure, XOR, record-transfer circuit, steering observer, exhaustive searches, rank, record and exit (Thm 7.1, Prop. I.9)", "checks/check_classes.py", 10, "Section 7, App. I"),
    ("Fiber law proof: dephasing is necessary and free; exact device vs entangled observers; distinguishable records; information-flow identity; robust bound on perturbed devices; steering observer alone is not enough (Lemmas I.1-I.8)", "checks/check_fiber.py", 60, "App. I"),
    ("Span criterion is sufficient, not necessary: Hadamard (B = capacity, unbalanced), X-dephasing (strict), energy dephasing (balanced) (Thm 4.3)", "checks/check_span_criterion.py", 5, "Section 4, App. H"),
    ("Two-qubit certificate: stabilizers, circuits, entropy bound on perturbed devices, every quoted number", "parts/law/check_certificate.py", 5, "Section 9, App. D"),
    ("Release rank: compiler exactness, rank identity, generalized Hamming weights, reset permutation, classical witness and its release order", "parts/law/check_release_rank.py", 5, "Section 5, App. E"),
    ("Release lemma, coherence surcharge, CNOT process, order-price matrix, delay law", "parts/law/check_beyond_thermo.py", 5, "Section 11, App. B--C"),
    ("Amplitude damping optimum m = h2(1/3); dephasing capacity; qutrit 0.1547", "parts/law/check_rates.py", 10, "Sections 5--6"),
    ("Speed--order collision model: A_K >= l^2/(2K), shared contact budget, intercept bias", "parts/law/check_speed_order.py", 5, "Section 9"),
    ("Processes: setting, work law identities, bookkeeping", "parts/module/check_setting.py", 10, "App. F"),
    ("Processes: the work law on random processes", "parts/module/check_law.py", 15, "App. F"),
    ("Processes: strong converse constants and entropy accumulation", "parts/module/check_converse.py", 30, "App. F"),
    ("Processes: free set and repair of small gain", "parts/module/check_free.py", 25, "App. F"),
    ("Processes: delay law", "parts/module/check_delay.py", 15, "App. F"),
    ("Processes: source factory and residue", "parts/module/check_factory.py", 5, "App. F"),
    ("Processes: hidden-bit (correlated) process", "parts/module/check_hidden_bit.py", 5, "App. F"),
    ("Processes: law without covariance (recorder and dual)", "parts/module/check_noncov.py", 15, "App. F"),
    ("Processes: order costs work, 1 - h(p)", "parts/module/check_order.py", 10, "App. F"),
    ("Processes: classical agents", "parts/module/check_agents.py", 5, "App. F"),
    ("Channels: the real-time law identities", "parts/channels/check_law.py", 5, "App. G"),
    ("Channels: classical channels pay no surcharge; flat-bath dilation; coherent-input correlation term", "parts/channels/check_classical.py", 5, "App. G"),
    ("Channels: Werner--Holevo support test and rates", "parts/channels/check_werner.py", 10, "App. G"),
    ("Channels: zero error removes the saving for extreme channels", "parts/channels/check_extreme.py", 10, "App. G"),
    ("Channels: finite saving at 234 and 256 uses", "parts/channels/check_finite_saving.py", 5, "App. G"),
    ("Channels: exact filters of the fixed-dimension reduction", "parts/channels/check_fixeddim.py", 5, "App. G"),
    ("Channels: free set, Gibbs defect, replacement", "parts/channels/check_free.py", 5, "App. G"),
    ("Channels: invertible environments bound", "parts/channels/check_invertible.py", 5, "App. G"),
    ("Channels: repeatable Schur channels outside the mixtures of unitaries (Haagerup-Musat Ex. 3.3 and a qubit example), one qubit of memory, correlated repeated outputs at trace distance 0.56", "parts/channels/check_repeatable.py", 5, "Section 12, App. G"),
    ("Channels: clock that returns approximately", "parts/channels/check_clock.py", 30, "App. G"),
    ("Channels: partial swaps and the qutrit process", "parts/channels/check_qutrit.py", 200, "App. G"),
    ("Channels: the explicit reset device and Hoeffding tail", "parts/channels/check_reset.py", 240, "App. G"),
    ("Clock: capital converse constants", "parts/batch/check_capital_converse.py", 50, "App. H"),
    ("Clock: what the clock costs", "parts/batch/check_clock_costs.py", 10, "App. H"),
    ("Clock: how large the clock must be; generator identity", "parts/batch/check_clock_size.py", 20, "App. H"),
    ("Clock: the batch law B(Phi), dual form, rare excitation", "parts/batch/check_batch_law.py", 120, "App. H"),
    ("Clock: examples, span criterion, X-dephasing", "parts/batch/check_examples.py", 25, "App. H"),
    ("Clock: a process and its time reverse (0.1547 kT)", "parts/batch/check_arrow.py", 30, "App. H"),
    ("Clock: controller that returns only in state", "parts/batch/check_embezzle.py", 5, "App. H"),
    ("Clock: noise horizon envelopes", "parts/batch/check_noise_horizon.py", 45, "App. H"),
]
NEGATIVE = [
    ("Identity must fail for a non-conserving unitary", "checks/check_identity.py", "--perturb"),
    ("Real-time fiber price must fail when replaced by the naive class count", "checks/check_classes.py", "--perturb"),
    ("Skipping dephasing, or using the steering observer alone, must fail", "checks/check_fiber.py", "--perturb"),
    ("Unbalanced-implies-strict-excess must fail on the Hadamard gate", "checks/check_span_criterion.py", "--perturb"),
    ("Protocol bound must fail when 1 - h2(delta) becomes 1 - delta, the embezzling distance when it becomes 1/n, and the graded-control curve when h2(eta) becomes 2 eta", "checks/check_protocol_numbers.py", "--perturb"),
]
LEAN = [
    ("Lean: release rank, reset permutation, certificate", "parts/law/check_lean.py"),
    ("Lean: process constants, binning, assembly", "parts/module/check_lean.py"),
    ("Lean: Werner--Holevo, qutrit, reset, finite device", "parts/channels/check_lean.py"),
    ("Lean: clock ladder, sinc bounds, permutations", "parts/batch/check_lean.py"),
]

def run(path, extra=(), timeout=1800):
    t0 = time.time()
    p = HERE / path
    try:
        r = subprocess.run([sys.executable, p.name, *extra], cwd=p.parent, capture_output=True, text=True, timeout=timeout)
        rc, out = r.returncode, (r.stdout + r.stderr)
    except subprocess.TimeoutExpired:
        rc, out = 124, 'timeout'
    return rc, out, time.time() - t0

def load_results():
    f = HERE / 'results.json'
    return json.loads(f.read_text()) if f.exists() else {}

def save_results(res):
    (HERE / 'results.json').write_text(json.dumps(res, indent=1))

def main():
    quick = '--quick' in ARGS
    select = None
    if '--select' in ARGS:
        select = sys.argv[sys.argv.index('--select') + 1]
    rows, ok_all = [], True
    if '--report' in ARGS:
        res = load_results()
        for claim, path, est, where in CHECKS:
            r = res.get(path)
            if r is None:
                rows.append((claim, path, 'NOT RUN', 0.0, where)); ok_all = False
            else:
                rows.append((claim, path, r['result'], r['seconds'], where)); ok_all &= (r['result'] == 'PASS')
    elif '--negative' in ARGS:
        for claim, path, flag in NEGATIVE:
            rc, out, dt = run(path, (flag,))
            fired = rc == 0 and 'negative control fired' in out
            ok_all &= fired
            rows.append((claim, path + ' ' + flag, 'CAUGHT' if fired else 'NOT CAUGHT', dt, ''))
            print(f"{'CAUGHT    ' if fired else 'NOT CAUGHT'} {claim}")
    else:
        selected = [c for c in CHECKS if (not quick or c[2] <= 60) and (select is None or select in c[1])]
        res = load_results()
        for claim, path, est, where in selected:
            print(f"== {path}  ({claim})", flush=True)
            rc, out, dt = run(path)
            passed = rc == 0 and 'All checks passed' in out
            blocked = (not passed) and ('ModuleNotFoundError' in out or 'ImportError' in out)
            ok_all &= passed
            tail = out.strip().splitlines()[-1] if out.strip() else ''
            status = 'PASS' if passed else ('BLOCKED' if blocked else 'FAIL')
            rows.append((claim, path, status, dt, where))
            res[path] = {'result': status, 'seconds': round(dt, 1), 'last_line': tail[:160]}
            save_results(res)
            print(f"   {status:7s}  {dt:6.1f}s  {tail[:100]}", flush=True)
        if '--lean' in ARGS:
            for claim, path in LEAN:
                rc, out, dt = run(path)
                passed = rc == 0
                ok_all &= passed
                rows.append((claim, path, 'PASS' if passed else 'FAIL', dt, 'formal'))
                print(f"   {'PASS' if passed else 'FAIL'}  {dt:6.1f}s  {claim}")
    # scorecard
    name = 'SCORECARD-NEGATIVE.md' if '--negative' in ARGS else 'SCORECARD.md'
    with open(HERE / name, 'w') as f:
        f.write('# Scorecard\n\n')
        f.write('Generated by `python3 verify.py' + (' --negative' if '--negative' in ARGS else ' --report' if '--report' in ARGS else ' --quick' if quick else '') + '`.\n\n')
        f.write('| Result | Claim | Script | Where | Seconds |\n|---|---|---|---|---|\n')
        for claim, path, res, dt, where in rows:
            f.write(f'| **{res}** | {claim} | `{path}` | {where} | {dt:.0f} |\n')
        f.write(f'\n**Overall: {"ALL PASSED" if ok_all else "FAILURES PRESENT"}** ({len(rows)} rows).\n')
    print()
    n_fail = sum(r[2] in ('FAIL', 'NOT CAUGHT') for r in rows); n_block = sum(r[2] == 'BLOCKED' for r in rows)
    if ok_all: verdict = 'ALL PASSED'
    elif n_fail == 0: verdict = f'NO FAILURES; {n_block} BLOCKED by a missing dependency (python -m pip install -r requirements.txt)'
    else: verdict = f'{n_fail} FAILED, {n_block} BLOCKED'
    print(f"{verdict}: {len(rows)} rows; scorecard written to {name}")
    sys.exit(0 if ok_all else 1)

if __name__ == '__main__':
    main()
