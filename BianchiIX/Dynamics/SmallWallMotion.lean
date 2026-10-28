import BianchiIX.Dynamics.KasnerGrowth
import BianchiIX.Dynamics.CoreContraction
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace BianchiIX

open Set

/-- A continuous path with a uniform one-positive-wall gap has a fixed growing wall. -/
theorem wall_growth_index_constant {α : ℝ → NormalizedState} {s t c : ℝ}
    (hst : s ≤ t) (hc : 0 < c) (hα : ContinuousOn α (Icc s t))
    (H : ∀ u ∈ Icc s t, ∃ i : Fin 3, c ≤ wallRate i (α u) ∧
      ∀ j : Fin 3, j ≠ i → wallRate j (α u) ≤ -c) :
    ∃ i : Fin 3, ∀ u ∈ Icc s t, c ≤ wallRate i (α u) ∧
      ∀ j : Fin 3, j ≠ i → wallRate j (α u) ≤ -c := by
  obtain ⟨i, hi, _⟩ := H s ⟨le_rfl, hst⟩
  have hnonzero (u : ℝ) (hu : u ∈ Icc s t) : wallRate i (α u) ≠ 0 := by
    obtain ⟨j, hj, hj'⟩ := H u hu
    by_cases heq : i = j
    · subst j
      exact (hc.trans_le hj).ne'
    · exact (lt_of_le_of_lt (hj' i heq) (neg_neg_of_pos hc)).ne
  refine ⟨i, ?_⟩
  intro u hu
  have hpos : 0 < wallRate i (α u) := by
    by_contra! hneg
    have hcont := (continuous_wallRate i).comp_continuousOn
      (hα.mono (Icc_subset_Icc le_rfl hu.2))
    obtain ⟨v, hv, heq⟩ := intermediate_value_Icc' hu.1 hcont
      (show (0 : ℝ) ∈ Icc (wallRate i (α u)) (wallRate i (α s)) from ⟨hneg, hc.le.trans hi⟩)
    exact hnonzero v ⟨hv.1, hv.2.trans hu.2⟩ heq
  obtain ⟨j, hj, hj'⟩ := H u hu
  have heq : i = j := by
    by_contra hne
    have hbad := hj' i hne
    linarith only [hbad, hpos, hc]
  simpa only [heq] using And.intro hj hj'

/-- Along an actual small-wall interval the growing wall increases exponentially and the other walls decrease. -/
theorem normalized_growth_gap_motion {x : NormalizedState} {T c : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x) (hT : 0 ≤ T) (hcpos : 0 < c)
    (H : ∀ u ∈ Icc 0 T, ∃ i : Fin 3, c ≤ wallRate i (normalizedMaxCurve x 0 u) ∧
      ∀ j : Fin 3, j ≠ i → wallRate j (normalizedMaxCurve x 0 u) ≤ -c) :
    ∃ i : Fin 3,
      (∀ u ∈ Icc 0 T, c ≤ wallRate i (normalizedMaxCurve x 0 u) ∧
        ∀ j : Fin 3, j ≠ i → wallRate j (normalizedMaxCurve x 0 u) ≤ -c) ∧
      StrictMonoOn (fun u => wallValue i (normalizedMaxCurve x 0 u)) (Icc 0 T) ∧
      (∀ j : Fin 3, j ≠ i → StrictAntiOn (fun u => wallValue j (normalizedMaxCurve x 0 u)) (Icc 0 T)) ∧
      wallValue i x * Real.exp (c * T) ≤ wallValue i (normalizedMaxCurve x 0 T) := by
  let α := normalizedMaxCurve x 0
  have hflow (u : ℝ) (hu : u ∈ Icc 0 T) : HasDerivAt α (normalizedField (α u)) u :=
    (normalizedMaxCurve_forward_of_constraint hc hu.1).1
  have hpos (u : ℝ) (hu : u ∈ Icc 0 T) (i : Fin 3) : 0 < wallValue i (α u) := by
    have hstart : 0 < wallValue i x := by fin_cases i <;> first | exact hp.1 | exact hp.2.1 | exact hp.2.2
    exact normalized_wall_pos (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
      (fun v hv => hasDerivAt_normalizedMaxCurve hv) (initial_mem_normalizedMaxDomain x 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hu.1) i
      (by simpa only [normalizedMaxCurve_initial] using hstart)
  obtain ⟨i, Hi⟩ := wall_growth_index_constant hT hcpos (HasDerivAt.continuousOn hflow) H
  have hd (j : Fin 3) (u : ℝ) (hu : u ∈ Icc 0 T) := hasDerivAt_wallValue (hflow u hu) j
  refine ⟨i, Hi, ?_, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Icc 0 T) (HasDerivAt.continuousOn (hd i))
    intro u hu
    rw [(hd i u (interior_subset hu)).deriv]
    exact mul_pos (hcpos.trans_le (Hi u (interior_subset hu)).1) (hpos u (interior_subset hu) i)
  · intro j hj
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 T) (HasDerivAt.continuousOn (hd j))
    intro u hu
    rw [(hd j u (interior_subset hu)).deriv]
    exact mul_neg_of_neg_of_pos
      ((Hi u (interior_subset hu)).2 j hj |>.trans_lt (neg_neg_of_pos hcpos))
      (hpos u (interior_subset hu) j)
  · have hh := le_exp_of_linear_deriv_le (convex_Icc 0 T)
      (fun u hu => (hd i u hu).neg) (c := c) (fun u hu => by
        have hb := mul_le_mul_of_nonneg_right (Hi u hu).1 (hpos u hu i).le
        change -(wallRate i (α u) * wallValue i (α u)) ≤ c * (-wallValue i (α u))
        nlinarith only [hb]) ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
    simpa only [Pi.neg_apply, α, normalizedMaxCurve_initial, sub_zero, neg_mul, neg_le_neg_iff] using hh

end BianchiIX
