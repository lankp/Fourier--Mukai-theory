## Your task: `wave8/universe-bridge` (effort: high)

Goal: make LP26 Theorem 1.1 and the compactness / generation notions apply to AxiomMath's
derived categories, whose Hom types live in `Type (u+1)` while their direct sums are indexed by
`Type u`.  The repository's `IsCompactAb`, `IsPaperGenerator`, `Coprod`, `InPreferredClass`,
`PaperWeakApproximationData` index sums by the Hom universe (`HasCoproducts.{v}`), which does not
fit (`wave7/spaces-compact-generation` found this).

1. Generalize, in `WeakApprox/` and `FourierMukai/Prelim/`, the notions and LP26 Theorem 1.1
   (`Spaces.Stacks.theorem_1_1` and what it uses) to a coproduct universe `w` independent of the
   Hom universe `v` (`HasCoproducts.{w}`, compactness against `w`-indexed sums), so that the old
   statements are the case `w = v`.  Keep every pinned statement: prove the old forms from the new.
2. Check non-vacuity at `w = u`, `v = u+1` on `Spaces.D` (AxiomMath's coproducts in
   `D(𝒪_X)`), and at `w = v` as before.
3. Bridges to AxiomMath's `IsCompactObject` at the new universes (`Spaces/Stacks/Bridges.lean`).

Branch `wave8/universe-bridge` from `origin/formalization`.  Files: `WeakApprox/`,
`FourierMukai/Prelim/`, `Spaces/Stacks/`, root import files, the two `Audit.lean`.  Do not edit
the baselines; if a pinned statement must change, stop and report.  Seven verification steps,
default build and both statement checks.
