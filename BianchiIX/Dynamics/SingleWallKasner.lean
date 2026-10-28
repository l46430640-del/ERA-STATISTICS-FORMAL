import BianchiIX.Algebra.SingleWallKasner
import BianchiIX.Dynamics.SingleStrongChart
import BianchiIX.Dynamics.SingleWallProjection

noncomputable section

namespace BianchiIX

theorem hasDerivAt_singleWallBeta {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t)
    (h3 : α t 3 = 0) (h4 : α t 4 = 0) (hp : 2 - α t 0 ≠ 0) :
    HasDerivAt (fun u => singleWallBeta (α u 0) (α u 1)) 0 t := by
  obtain ⟨hp', hs', _⟩ := hasDerivAt_normalized_components hα
  apply (hs'.div (hp'.const_sub 2) hp).congr_deriv
  simp only [h3, h4]
  dsimp [shearPlus, shearMinus, curvature]
  ring

/-- The straight-line coordinate is conserved along the exact maximal single-wall flow. -/
theorem normalized_singleWall_beta_constant {x : NormalizedState} {t₀ t : ℝ}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (ht : t ∈ normalizedMaxDomain x t₀) :
    singleWallBeta (normalizedMaxCurve x t₀ t 0) (normalizedMaxCurve x t₀ t 1) =
      singleWallBeta (x 0) (x 1) := by
  have hd (u : ℝ) (hu : u ∈ normalizedMaxDomain x t₀) :
      HasDerivAt (fun v => singleWallBeta (normalizedMaxCurve x t₀ v 0) (normalizedMaxCurve x t₀ v 1)) 0 u := by
    obtain ⟨hu3, hu4⟩ := normalized_single_strong_zeros h3 h4 hu
    have hc' : constraint (normalizedMaxCurve x t₀ u 0) (normalizedMaxCurve x t₀ u 1)
        (normalizedMaxCurve x t₀ u 2) 0 0 = 1 := by
      simpa only [stateConstraint, hu3, hu4] using (normalizedMaxCurve_constraint hu).trans hc
    have hp := (singleWall_shear_bounds hc').2.2.1
    exact hasDerivAt_singleWallBeta (hasDerivAt_normalizedMaxCurve hu) hu3 hu4 (by linarith only [hp])
  have H := (convex_normalizedMaxDomain x t₀).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hd u hu).hasDerivWithinAt) (C := 0) (fun _ _ => by simp)
    (initial_mem_normalizedMaxDomain x t₀) ht
  simpa [sub_eq_zero, normalizedMaxCurve_initial] using H

/-- The exact scalar equation, in the original normalized time. -/
theorem normalized_singleWall_reduced {x : NormalizedState} {t₀ t : ℝ}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (ht : t ∈ normalizedMaxDomain x t₀) :
    let β := singleWallBeta (x 0) (x 1)
    let ξ := singleWallXi β (normalizedMaxCurve x t₀ t 0)
    normalizedMaxCurve x t₀ t 2 ^ 2 = (singleWallChi β ^ 2 - ξ ^ 2) / (1 + β ^ 2) ∧
      rateOne (normalizedMaxCurve x t₀ t 0) (normalizedMaxCurve x t₀ t 1) =
        (2 - normalizedMaxCurve x t₀ t 0) * ξ ∧
      HasDerivAt (fun u => singleWallXi β (normalizedMaxCurve x t₀ u 0))
        (-(2 - ξ) * (singleWallChi β ^ 2 - ξ ^ 2) / (1 + β ^ 2)) t := by
  dsimp only
  let β := singleWallBeta (x 0) (x 1)
  let p := normalizedMaxCurve x t₀ t 0
  let s := normalizedMaxCurve x t₀ t 1
  let n := normalizedMaxCurve x t₀ t 2
  obtain ⟨ht3, ht4⟩ := normalized_single_strong_zeros h3 h4 ht
  have hc' : constraint p s n 0 0 = 1 := by
    simpa only [stateConstraint, ht3, ht4] using (normalizedMaxCurve_constraint ht).trans hc
  have hp := (singleWall_shear_bounds hc').2.2.1
  have hline : s = β * (2 - p) := by
    have H := singleWall_beta_line (s := s) (show 2 - p ≠ 0 by linarith only [hp])
    rw [normalized_singleWall_beta_constant hc h3 h4 ht] at H
    exact H
  obtain ⟨heq, hrate, hfield⟩ := singleWall_reduction hc' hline
  have ha : 0 < 1 + β ^ 2 := by positivity
  have hrad : 0 ≤ 1 - 3 * β ^ 2 := by
    nlinarith only [heq, mul_nonneg ha.le (sq_nonneg n), sq_nonneg (singleWallXi β p)]
  have hχ : singleWallChi β ^ 2 = 1 - 3 * β ^ 2 := Real.sq_sqrt hrad
  have hn : n ^ 2 = (singleWallChi β ^ 2 - singleWallXi β p ^ 2) / (1 + β ^ 2) := by
    apply (eq_div_iff ha.ne').mpr
    nlinarith only [heq, hχ]
  refine ⟨hn, hrate, ?_⟩
  have hd := ((hasDerivAt_pi.mp (hasDerivAt_normalizedMaxCurve ht) 0).const_mul (1 + β ^ 2)).sub_const (2 * β ^ 2)
  change HasDerivAt (fun u => singleWallXi β (normalizedMaxCurve x t₀ u 0)) _ t at hd
  apply hd.congr_deriv
  change (1 + β ^ 2) * shearPlus p n _ _ = _
  rw [ht3, ht4, hfield, hn]
  ring

theorem normalized_singleWall_log_deriv {x : NormalizedState} {t₀ t : ℝ}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hn : 0 < x 2) (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (fun u => Real.log (normalizedMaxCurve x t₀ u 2))
      ((2 - normalizedMaxCurve x t₀ t 0) *
        singleWallXi (singleWallBeta (x 0) (x 1)) (normalizedMaxCurve x t₀ t 0)) t := by
  have hn' : 0 < normalizedMaxCurve x t₀ t 2 := by
    have H := normalized_wall_pos (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht 0
    exact H (by simpa only [normalizedMaxCurve_initial, wallValue] using! hn)
  have H := (hasDerivAt_pi.mp (hasDerivAt_normalizedMaxCurve ht) 2).log hn'.ne'
  convert H using 1
  change _ = rateOne (normalizedMaxCurve x t₀ t 0) (normalizedMaxCurve x t₀ t 1) *
    normalizedMaxCurve x t₀ t 2 / normalizedMaxCurve x t₀ t 2
  rw [mul_div_cancel_right₀ _ hn'.ne', (normalized_singleWall_reduced hc h3 h4 ht).2.1]

def singleWallIncomingState (x : NormalizedState) : NormalizedState :=
  ![singleWallIncomingPlus (singleWallBeta (x 0) (x 1)),
    singleWallIncomingMinus (singleWallBeta (x 0) (x 1)), 0, 0, 0]

theorem singleWall_incoming_state_bounds {x : NormalizedState} {g : ℝ}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hn : 0 ≤ x 2) (hg : 0 < g) (hr : g ≤ rateOne (x 0) (x 1)) :
    stateConstraint (singleWallIncomingState x) = 1 ∧
      0 < rateOne (singleWallIncomingState x 0) (singleWallIncomingState x 1) ∧
      normalizedEuclideanDistance (singleWallIncomingState x) x ≤ x 2 + 2 * x 2 ^ 2 / g := by
  let β := singleWallBeta (x 0) (x 1)
  have hc' : constraint (x 0) (x 1) (x 2) 0 0 = 1 := by simpa only [stateConstraint, h3, h4] using hc
  have hp := (singleWall_shear_bounds hc').2.2.1
  have hline := singleWall_beta_line (s := x 1) (show 2 - x 0 ≠ 0 by linarith only [hp])
  have hb := singleWall_upward_bounds hc' hline hg hr
  have hrad : 0 ≤ 1 - 3 * β ^ 2 := by nlinarith only [hb.2.1]
  obtain ⟨hcircle, hξ⟩ := singleWall_incoming_circle hrad
  have hcon : stateConstraint (singleWallIncomingState x) = 1 := by
    simpa [stateConstraint, constraint, curvature, singleWallIncomingState] using hcircle
  have hcon' : constraint (singleWallIncomingPlus β) (singleWallIncomingMinus β) 0 0 0 = 1 := hcon
  have hpin := (singleWall_shear_bounds hcon').2.2.1
  have hrate := (singleWall_reduction hcon' (by rfl)).2.1
  have hχpos : 0 < singleWallChi β := hb.2.2.2.2.1.trans_le hb.2.2.2.2.2.1
  refine ⟨hcon, ?_, ?_⟩
  · change 0 < rateOne (singleWallIncomingPlus β) (singleWallIncomingMinus β)
    rw [hrate, hξ]
    exact mul_pos (by linarith only [hpin]) hχpos
  · let d := Real.sqrt ((singleWallIncomingPlus β - x 0) ^ 2 + (singleWallIncomingMinus β - x 1) ^ 2)
    have hd : d ≤ 2 * x 2 ^ 2 / g := (singleWall_incoming_displacement hc' hline hg hr).2.2.2
    have hd0 : 0 ≤ d := Real.sqrt_nonneg _
    have hdsq : d ^ 2 = (singleWallIncomingPlus β - x 0) ^ 2 + (singleWallIncomingMinus β - x 1) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have H := normalizedEuclideanDistance_sq (singleWallIncomingState x) x
    simp [Fin.sum_univ_succ, singleWallIncomingState, h3, h4] at H
    change normalizedEuclideanDistance (singleWallIncomingState x) x ^ 2 = _ at H
    change d ^ 2 = (singleWallIncomingPlus (singleWallBeta (x 0) (x 1)) - x 0) ^ 2 +
      (singleWallIncomingMinus (singleWallBeta (x 0) (x 1)) - x 1) ^ 2 at hdsq
    have Hdist : normalizedEuclideanDistance (singleWallIncomingState x) x ≤ x 2 + d := by
      nlinarith only [H, hdsq, mul_nonneg hn hd0, hn, hd0,
        normalizedEuclideanDistance_nonneg (singleWallIncomingState x) x]
    linarith only [Hdist, hd]

/-- The physical entry is close to a growing Kasner state with an explicit uniform error. -/
theorem projected_incoming_state_bounds {x : NormalizedState} {Δ c : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hnmax : x 2 ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ x 2 / 8)
    (hprod : normalizedWallProductsBound Δ x) (hcpos : 0 < c)
    (hr : c ≤ rateOne (x 0) (x 1)) (hsmall : Δ ^ 2 ≤ c / 18) :
    let z := singleWallIncomingState (singleWallProjection x)
    stateConstraint z = 1 ∧ 0 < rateOne (z 0) (z 1) ∧
      normalizedEuclideanDistance z x ≤ 2 * Δ ^ 2 / x 2 + x 2 + 4 * x 2 ^ 2 / c := by
  let y := singleWallProjection x
  let z := singleWallIncomingState y
  have H := normalized_singleWall_projection hc hp hnmax hΔ hprod
  have Hy := singleWall_incoming_state_bounds H.1 H.2.2.1 H.2.2.2.1 hp.1.le (half_pos hcpos)
    (singleWall_projection_growth hc hp hnmax hΔ hprod hr hsmall)
  refine ⟨Hy.1, Hy.2.1, ?_⟩
  have Htri : normalizedEuclideanDistance z x ≤ normalizedEuclideanDistance z y + normalizedEuclideanDistance y x :=
    dist_triangle _ _ _
  have Hdist : normalizedEuclideanDistance z y ≤ x 2 + 4 * x 2 ^ 2 / c := by
    convert Hy.2.2 using 1
    change x 2 + 4 * x 2 ^ 2 / c = x 2 + 2 * x 2 ^ 2 / (c / 2)
    ring
  have Hxy : normalizedEuclideanDistance y x ≤ 2 * Δ ^ 2 / x 2 := H.2.2.2.2.2.1
  change normalizedEuclideanDistance z x ≤ _
  linarith only [Htri, Hdist, Hxy]

end BianchiIX
