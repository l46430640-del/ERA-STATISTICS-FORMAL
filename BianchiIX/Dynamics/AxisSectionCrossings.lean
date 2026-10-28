import BianchiIX.Dynamics.AxisPermutations
import BianchiIX.Analysis.SectionCrossings

noncomputable section

namespace BianchiIX

open Set

def axisSectionTimes (A : NormalizedSymmetry) (h ε : ℝ) (x : NormalizedState) (t₀ T : ℝ) : Set ℝ :=
  {t ∈ Icc t₀ T | A.map (normalizedMaxCurve x t₀ t) 2 = h ∧
    A.map (normalizedMaxCurve x t₀ t) 0 ≤ -ε}

theorem finite_axisSectionTimes (A : NormalizedSymmetry) {h ε t₀ T : ℝ} {x : NormalizedState}
    (hh : 0 < h) (hε : 0 < ε) (hpos : positiveWalls x) (hcon : stateConstraint x = 1) :
    (axisSectionTimes A h ε x t₀ T).Finite := by
  let S := (maximalNormalizedSolution x t₀).transform A
  have hd (t : ℝ) (ht : t ∈ Icc t₀ T) := hasDerivAt_normalized_components
    (S.hasDerivAt t (normalizedMaxDomain_contains_Ici hpos hcon t₀ ht.1))
  exact finite_negative_section_times isCompact_Icc
    (fun t ht => (hd t ht).2.2.1.continuousAt.continuousWithinAt)
    (fun t ht => (hd t ht).1.continuousAt.continuousWithinAt) hh hε
    (fun t ht => (hd t ht).2.2.1)

/-- A finite family of axis sections has only finitely many intersections on every finite future interval. -/
theorem finite_axisSectionTimes_iUnion {ι : Type*} [Finite ι]
    (A : ι → NormalizedSymmetry) {h ε : ι → ℝ} {x : NormalizedState} {t₀ T : ℝ}
    (hh : ∀ i, 0 < h i) (hε : ∀ i, 0 < ε i)
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1) :
    (⋃ i, axisSectionTimes (A i) (h i) (ε i) x t₀ T).Finite :=
  Set.finite_iUnion (fun i => finite_axisSectionTimes (A i) (hh i) (hε i) hpos hcon)

end BianchiIX
