import BianchiIX.Algebra.KasnerRates
import BianchiIX.Dynamics.TaubDistance
import BianchiIX.Dynamics.ConstrainedComplete
import Mathlib.Topology.Order.Compact

noncomputable section

namespace BianchiIX

open Set

def wallGrowthMargin (x : NormalizedState) : ℝ :=
  max (min (wallRate 0 x) (min (-wallRate 1 x) (-wallRate 2 x)))
    (max (min (wallRate 1 x) (min (-wallRate 0 x) (-wallRate 2 x)))
      (min (wallRate 2 x) (min (-wallRate 0 x) (-wallRate 1 x))))

theorem continuous_wallGrowthMargin : Continuous wallGrowthMargin := by
  exact ((continuous_wallRate 0).min ((continuous_wallRate 1).neg.min (continuous_wallRate 2).neg)).max
    (((continuous_wallRate 1).min ((continuous_wallRate 0).neg.min (continuous_wallRate 2).neg)).max
      ((continuous_wallRate 2).min ((continuous_wallRate 0).neg.min (continuous_wallRate 1).neg)))

theorem exists_wall_rate_margin_of_le {x : NormalizedState} {c : ℝ} (h : c ≤ wallGrowthMargin x) :
    ∃ i : Fin 3, c ≤ wallRate i x ∧ ∀ j : Fin 3, j ≠ i → wallRate j x ≤ -c := by
  rcases le_max_iff.mp h with h | h
  · obtain ⟨h0, h1, h2⟩ := (le_min_iff.mp h).imp_right le_min_iff.mp
    refine ⟨0, h0, ?_⟩
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · simpa only [neg_neg] using! neg_le_neg h1
    · simpa only [neg_neg] using! neg_le_neg h2
  · rcases le_max_iff.mp h with h | h
    · obtain ⟨h1, h0, h2⟩ := (le_min_iff.mp h).imp_right le_min_iff.mp
      refine ⟨1, h1, ?_⟩
      intro j hj
      fin_cases j
      · simpa only [neg_neg] using! neg_le_neg h0
      · exact (hj rfl).elim
      · simpa only [neg_neg] using! neg_le_neg h2
    · obtain ⟨h2, h0, h1⟩ := (le_min_iff.mp h).imp_right le_min_iff.mp
      refine ⟨2, h2, ?_⟩
      intro j hj
      fin_cases j
      · simpa only [neg_neg] using! neg_le_neg h0
      · simpa only [neg_neg] using! neg_le_neg h1
      · exact (hj rfl).elim

theorem normalized_kasner_growth_margin_pos {x : NormalizedState}
    (hc : stateConstraint x = 1) (h2 : x 2 = 0) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hnot : ∀ i : Fin 3, x ≠ taubPoint i) : 0 < wallGrowthMargin x := by
  have hcircle : shearSq (x 0) (x 1) = 1 := by
    simpa only [stateConstraint, constraint, curvature, h2, h3, h4, zero_pow (by omega : 2 ≠ 0),
      mul_zero, zero_mul, add_zero, sub_zero] using hc
  have hsq : x 0 ^ 2 + x 1 ^ 2 = 1 := hcircle
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : x 0 ≠ -1 := by
    intro heq
    have hs : x 1 = 0 := by nlinarith only [hsq, heq]
    apply hnot 0
    change x = ![-1, 0, 0, 0, 0]
    ext j
    fin_cases j <;> first | exact heq | exact hs | exact h2 | exact h3 | exact h4
  have hp' : x 0 ≠ 1 / 2 := by
    intro heq
    have hfactor : (x 1 - Real.sqrt 3 / 2) * (x 1 + Real.sqrt 3 / 2) = 0 := by
      nlinarith only [hsq, heq, hsqrt]
    rcases mul_eq_zero.mp hfactor with hs | hs
    · have hs' : x 1 = Real.sqrt 3 / 2 := by linarith only [hs]
      apply hnot 2
      change x = ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]
      ext j
      fin_cases j <;> first | exact heq | exact hs' | exact h2 | exact h3 | exact h4
    · have hs' : x 1 = -Real.sqrt 3 / 2 := by linarith only [hs]
      apply hnot 1
      change x = ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0]
      ext j
      fin_cases j <;> first | exact heq | exact hs' | exact h2 | exact h3 | exact h4
  rcases kasner_growth_signs hcircle hp hp' with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact lt_max_of_lt_left (lt_min h0 (lt_min (neg_pos.mpr h1) (neg_pos.mpr h2)))
  · exact lt_max_of_lt_right (lt_max_of_lt_left (lt_min h1 (lt_min (neg_pos.mpr h0) (neg_pos.mpr h2))))
  · exact lt_max_of_lt_right (lt_max_of_lt_right (lt_min h2 (lt_min (neg_pos.mpr h0) (neg_pos.mpr h1))))

/-- Uniformly away from Taub, all sufficiently small-wall states have one growing and two decaying walls. -/
theorem exists_smallWall_growth_gap {ε : ℝ} (hε : 0 < ε) :
    ∃ ν > (0 : ℝ), ν ≤ 1 / 4 ∧ ∃ c > (0 : ℝ), c ≤ 1 ∧
      ∀ x : NormalizedState, stateConstraint x = 1 →
        (∀ i : Fin 3, wallValue i x ∈ Icc 0 ν) →
        (∀ i : Fin 3, ε ≤ normalizedEuclideanDistance x (taubPoint i)) →
        ∃ i : Fin 3, c ≤ wallRate i x ∧ ∀ j : Fin 3, j ≠ i → wallRate j x ≤ -c := by
  let K : Set NormalizedState := {x | stateConstraint x = 1 ∧
    (∀ i : Fin 3, wallValue i x ∈ Icc 0 1) ∧
    ∀ i : Fin 3, ε ≤ normalizedEuclideanDistance x (taubPoint i)}
  have hKw : IsClosed {x : NormalizedState | ∀ i : Fin 3, wallValue i x ∈ Icc 0 1} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_apply (i.addNat 2)))
  have hKd : IsClosed {x : NormalizedState | ∀ i : Fin 3, ε ≤ normalizedEuclideanDistance x (taubPoint i)} := by
    have hd (i : Fin 3) : Continuous (fun x : NormalizedState => normalizedEuclideanDistance x (taubPoint i)) :=
      continuous_normalizedEuclideanDistance.comp (f := fun x : NormalizedState => (x, taubPoint i))
        (continuous_id.prodMk continuous_const)
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le continuous_const (hd i))
  have hKclosed : IsClosed K :=
    (isClosed_eq (contDiff_stateConstraint 1).continuous continuous_const).inter (hKw.inter hKd)
  have hK : IsCompact K := (isCompact_closedBall (0 : NormalizedState) 4).of_isClosed_subset hKclosed (by
    intro x hx
    have hb := normalizedState_norm_bound_abs hx.1 (fun i =>
      (abs_of_nonneg (hx.2.1 i).1).trans_le (hx.2.1 i).2)
    simpa only [Metric.mem_closedBall, dist_zero_right, mul_one, show (1 : ℝ) + 3 = 4 by norm_num] using hb)
  let F : NormalizedState → ℝ := fun x => max (wallGrowthMargin x) (x 2 + x 3 + x 4)
  have hF : Continuous F := continuous_wallGrowthMargin.max (by fun_prop)
  have hFpos (x : NormalizedState) (hx : x ∈ K) : 0 < F x := by
    have h2 : 0 ≤ x 2 := (hx.2.1 0).1
    have h3 : 0 ≤ x 3 := (hx.2.1 1).1
    have h4 : 0 ≤ x 4 := (hx.2.1 2).1
    by_cases hh : 0 < x 2 + x 3 + x 4
    · exact lt_max_of_lt_right hh
    · have hz2 : x 2 = 0 := by linarith only [h2, h3, h4, not_lt.mp hh]
      have hz3 : x 3 = 0 := by linarith only [h2, h3, h4, not_lt.mp hh]
      have hz4 : x 4 = 0 := by linarith only [h2, h3, h4, not_lt.mp hh]
      apply lt_max_of_lt_left
      apply normalized_kasner_growth_margin_pos hx.1 hz2 hz3 hz4
      intro i heq
      have hd := hx.2.2 i
      rw [heq] at hd
      have hz : normalizedEuclideanDistance (taubPoint i) (taubPoint i) = 0 := dist_self _
      rw [hz] at hd
      exact (not_le_of_gt hε) hd
  obtain ⟨d, hd, H⟩ := hK.exists_forall_le' hF.continuousOn hFpos
  let ν := min (1 / 4) (d / 6)
  let c := min 1 d
  have hν : 0 < ν := lt_min (by norm_num) (by positivity)
  refine ⟨ν, hν, min_le_left _ _, c, lt_min zero_lt_one hd, min_le_left _ _, ?_⟩
  intro x hc hw ha
  have hx : x ∈ K := ⟨hc, fun i => ⟨(hw i).1,
    (hw i).2.trans ((min_le_left _ _).trans (by norm_num : (1 / 4 : ℝ) ≤ 1))⟩, ha⟩
  have hs : x 2 + x 3 + x 4 ≤ d / 2 := by
    have h2 : x 2 ≤ ν := (hw 0).2
    have h3 : x 3 ≤ ν := (hw 1).2
    have h4 : x 4 ≤ ν := (hw 2).2
    have hνd : ν ≤ d / 6 := min_le_right _ _
    linarith only [h2, h3, h4, hνd]
  have hm : d ≤ wallGrowthMargin x := by
    rcases le_max_iff.mp (H x hx) with hh | hh
    · exact hh
    · linarith only [hh, hs, hd]
  exact exists_wall_rate_margin_of_le ((min_le_right _ _).trans hm)

end BianchiIX
