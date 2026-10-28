# Era Statistics for the Vacuum Bianchi IX Flow

Lean 4 proofs concerning era statistics for the exact normalized vacuum
Bianchi IX equations with zero cosmological constant.

The main declaration is
[`BianchiIX.exists_full_measure_era_statistics`](BianchiIX/Statistics/FullMeasureStatistics.lean).
It is conditional on the two explicit literature propositions described below.
The starting point is the normalized ordinary differential equation, defined in
[`Algebra/Flow.lean`](BianchiIX/Algebra/Flow.lean) and
[`Dynamics/Normalized.lean`](BianchiIX/Dynamics/Normalized.lean).

## Mathematical Scope

The final theorem constructs one invariant Borel exceptional set, null in
transverse coordinates and regular four-dimensional constraint coordinates,
including measures with densities. Outside it there are measurable choices of
complete eras along the same exact trajectory. Their entrance times are
positive, strictly increasing, and unbounded.

[`PhysicalEraSequence`](BianchiIX/Statistics/PhysicalEraSequence.lean) records
the actual core crossings, axis frames, connecting events, and a terminal
connection preceding the first selected era.
[`PhysicalEraObservables`](BianchiIX/Statistics/PhysicalEraObservables.lean)
identifies the era length with the number of cores and the integer part of the
entrance era parameter. The statistical conclusions are collected in
[`EraStatistics`](BianchiIX/Statistics/EraStatistics.lean):

- Gauss averages for every continuous phase observable;
- frequencies of every finite block of positive era lengths;
- the single-length and tail distributions;
- logarithmic growth of the limiting truncated mean;
- divergence of the untruncated mean era length.

Sampling assigns equal weight to each era. The formalization starts from the
normalized ODE; deriving that system from a spacetime metric and statistics
weighted by physical duration are outside this theorem's statement.

## Explicit Literature Inputs

The main theorem has exactly these two proposition parameters:

1. [`Literature.BirkhoffErgodicInput`](BianchiIX/Literature.lean), instantiated
   at `Real`: Birkhoff's pointwise ergodic theorem for real-valued integrable
   functions on an ergodic probability space. A reference is C. Walkden,
   *Ergodic Theory*, Corollary 10.1.2, printed page 89
   ([lecture notes](https://personalpages.manchester.ac.uk/staff/Charles.Walkden/ergodic-theory/ergodic_theory.pdf)).
2. [`Literature.BrehmIXAttractorInput`](BianchiIX/Literature/Attractor.lean):
   the complementary curvature-wall quantities tend to zero along positive-wall
   Bianchi IX trajectories outside the Taub subspaces. This is the consequence
   of B. Brehm's local attractor Theorem 2, equation (6.2c), and Bianchi IX
   global Theorem 3, Section 6, pages 44-45 of
   [arXiv:1606.08058v1](https://arxiv.org/abs/1606.08058v1).

These propositions are defined in Lean and passed as hypotheses. They are not
new Lean axioms. In particular the attractor input assumes neither statistical
typicality nor a transverse measure conclusion. Successful verification checks
the implication from these inputs; it does not supply formal proofs of the
literature inputs themselves.

## Reproduce the Verification

Requirements: Git, Python 3.11 or later, and
[elan](https://github.com/leanprover/elan). The checked configuration pins:

- Lean `v4.33.1` in `lean-toolchain`;
- mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` in
  `lakefile.toml` and `lake-manifest.json`;
- transitive dependencies in the same lockfile.

Run from the repository root:

```sh
export LEAN_NUM_THREADS=2
python3 scripts/check_sources.py
python3 scripts/fetch_mathlib_cache.py
lake --wfail build BianchiIX
lake env lean -j2 -DwarningAsError=true Audit.lean
lake env leanchecker BianchiIX.Statistics.FullMeasureStatistics
```

In PowerShell, set `$env:LEAN_NUM_THREADS = "2"` instead of using `export`,
and use `python` if that is the Python executable's name.
The cache helper downloads only the upstream modules imported by the project
and their dependencies. It does not download compiled copies of this project's
proofs. Avoid `lake update` when reproducing this pinned version.
Compilation is substantial. The commands set `LEAN_NUM_THREADS=2`,
and the library configuration also limits each Lean process to two threads.
Build outputs and dependency caches are ignored by Git.

[`Audit.lean`](Audit.lean) recursively inspects the axiom dependencies of every
declaration in the `BianchiIX` namespace, including private declarations.
The allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
The source check also verifies the import inventory, pinned dependency sources,
and the absence of proof placeholders and project axiom declarations.
The final command replays the final theorem module with Lean's kernel checker.

The [verification workflow](.github/workflows/verify.yml) runs these checks on
GitHub. Results are retained in the repository's
[Actions history](https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/actions/workflows/verify.yml).
Repository access is currently restricted, so these links require authorization.

## Source Organization

| Directory | Contents |
|---|---|
| `BianchiIX/Algebra` | Exact vector fields, coordinate identities, and algebraic bounds |
| `BianchiIX/Analysis` | Analytic estimates, variation bounds, and event regularity |
| `BianchiIX/Dynamics` | Exact flows, core passages, connections, and era events |
| `BianchiIX/Measure` | Section flux, null-set transport, and capture arguments |
| `BianchiIX/Statistics` | Gauss coding, statistical transfer, and the final theorem |
| `BianchiIX/Literature` | The attractor input and its direct consequences |

`BianchiIX.lean` imports all project modules. For the final result alone, import
`BianchiIX.Statistics.FullMeasureStatistics`.

## License

The project sources and verification tooling are distributed under the
[MIT License](LICENSE). Lean, mathlib, and other dependencies retain their own
licenses and are obtained separately through the pinned build configuration.
