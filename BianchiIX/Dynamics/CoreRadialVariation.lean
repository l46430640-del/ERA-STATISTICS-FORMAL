import BianchiIX.Dynamics.CoreStrongIntegrals
import BianchiIX.Dynamics.CoreWeightIntegrals
import BianchiIX.Dynamics.CoreAmplitudeBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem coreRegion_radius_variation_row {k Q : ℝ} {y : ProjectiveState} {v : CoreAngleState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hQ : ‖v‖ ≤ Q) :
    let B := coreWeightedJacobian k (projectiveCoreAngle y) (toCoreAngleState y)
    |B.mulVec v 0| ≤
      (16 * y 1 + 8 / k ^ 2 * y 3 ^ 2 + 8 * (y 3 / (k * y 2))) * Q +
        2 * (|v 1| / Real.cosh (projectiveCoreAngle y)) + (1 / k) * |v 1| := by
  intro B
  have hk0 : 0 < k := by linarith only [hk]
  have hv : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hu0 := hy.2.2.1.1
  have hw0 := (coreRegion_wall_bounds hy).2.1
  have hQ0 : 0 ≤ Q := (norm_nonneg v).trans hQ
  have hc (i : Fin 3) : |v i| ≤ Q := (show |v i| ≤ ‖v‖ from norm_le_pi_norm v i).trans hQ
  obtain ⟨h00, h01, h02⟩ := coreRegion_amplitude_row_bounds hk hy
  change |B 0 1 + y 2 / k| ≤ 8 * (y 1 + y 3) / k at h01
  have hsmall : 8 * (y 1 + y 3) ≤ 1 := by
    have hu := coreBootstrap_wall_bound hk hy.2.2.1.2
    have hw := coreBootstrap_wall_bound hk (coreRegion_wall_bounds hy).2.2
    linarith only [hu, hw]
  have h01' : |B 0 1| ≤ y 2 / k + 1 / k := by
    have H := abs_add_le (B 0 1 + y 2 / k) (-(y 2 / k))
    rw [add_neg_cancel_right, abs_neg, abs_of_pos (div_pos hv hk0)] at H
    exact H.trans (by linarith only [h01, div_le_div_of_nonneg_right hsmall hk0.le])
  have h02' : |B 0 2| ≤ 8 * y 1 + 8 * (y 3 / (k * y 2)) := by
    have hu := div_le_self hu0 hy.2.1
    have hid : 8 * (y 1 + y 3 / k) / y 2 = 8 * (y 1 / y 2) + 8 * (y 3 / (k * y 2)) := by ring
    exact h02.trans (by rw [hid]; linarith only [hu])
  have hvk : y 2 / k ≤ 2 / Real.cosh (projectiveCoreAngle y) := by
    rw [← (coreAngle_coordinates (m := y 0) hv).1]
    have hr : coreRadius (y 0) (y 2) ≤ 2 * k := by
      linarith only [(coreRegion_radius_bounds hk hy).2, hk]
    calc
      coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)) / k =
          (coreRadius (y 0) (y 2) / k) / Real.cosh (projectiveCoreAngle y) := by
            dsimp [projectiveCoreAngle]
            ring
      _ ≤ 2 / Real.cosh (projectiveCoreAngle y) :=
        div_le_div_of_nonneg_right ((div_le_iff₀ hk0).mpr hr) (Real.cosh_pos _).le
  have hrow : B.mulVec v 0 = B 0 0 * v 0 + B 0 1 * v 1 + B 0 2 * v 2 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]
  rw [hrow]
  calc
    _ ≤ |B 0 0| * |v 0| + |B 0 1| * |v 1| + |B 0 2| * |v 2| := by
      have H := (abs_add_le (B 0 0 * v 0 + B 0 1 * v 1) (B 0 2 * v 2)).trans
        (add_le_add (abs_add_le (B 0 0 * v 0) (B 0 1 * v 1)) (le_refl _))
      simpa only [abs_mul] using H
    _ ≤ (8 * (y 1 + y 3 ^ 2 / k ^ 2)) * Q +
        (2 / Real.cosh (projectiveCoreAngle y) + 1 / k) * |v 1| +
        (8 * y 1 + 8 * (y 3 / (k * y 2))) * Q := by
      exact add_le_add (add_le_add
        (mul_le_mul h00 (hc 0) (abs_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right (h01'.trans (add_le_add hvk (le_refl _))) (abs_nonneg _)))
        (mul_le_mul h02' (hc 2) (abs_nonneg _) (by positivity))
    _ = _ := by ring

private theorem core_radius_integral_constants {k U P Q X : ℝ}
    (hk : 6 ≤ k) (hU : 0 ≤ U) (hP : 0 ≤ P) (hPk : P ≤ k) (hQ : 0 ≤ Q) (hX : 0 ≤ X) :
    (16 * Q) * (4 * U / k) + (8 * Q / k ^ 2) * (2 * (101 / 99 : ℝ) ^ 2 * P ^ 2) +
        (8 * Q) * (2 * (101 / 99 : ℝ) ^ 2 * P / k) +
        2 * ((12 * X + 432 * U * Q) / k ^ 2) + (1 / k) * ((4 * X + 48 * U * Q) / k) ≤
      256 * (X / k ^ 2 + (U + P) * Q / k) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hUk := mul_le_mul_of_nonneg_right hk (mul_nonneg hU hQ)
  have hP2 := mul_le_mul_of_nonneg_right hPk (mul_nonneg hP hQ)
  have hUQk := mul_nonneg (mul_nonneg hU hQ) hk0.le
  have hPQk := mul_nonneg (mul_nonneg hP hQ) hk0.le
  have hP2Q := mul_nonneg (sq_nonneg P) hQ
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hk0)).mp
  field_simp
  nlinarith only [hX, hUk, hP2, hUQk, hPQk, hP2Q]

/-- The radius component of the genuine fixed-angle variation has an integrable amplitude-sensitive drift. -/
theorem coreProjectedFlowVariation_radius_drift {y : ProjectiveState} {t₀ k a b Q : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b) (hD : 0 < projectiveStateDenom y)
    (hdom : Icc a b ⊆ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : ∀ t ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hcore : ∀ t ∈ Icc a b, coreRegion k (projectiveOriginalFlow y t₀ t))
    (hentry : Real.cosh (projectiveCoreAngle (projectiveOriginalFlow y t₀ a)) = k)
    (w : ProjectiveState)
    (hQ : ∀ t ∈ Icc a b, ‖scaleCoreVariation k (coreProjectedFlowVariation y t₀ t w)‖ ≤ Q) :
    let β := projectiveOriginalFlow y t₀
    let ξ := fun t => coreProjectedFlowVariation y t₀ t w
    |ξ b 0 - ξ a 0| ≤ 256 * (|k * ξ a 1| / k ^ 2 + (β a 1 + β a 2 * β a 3) * Q / k) := by
  intro β ξ
  let θ := fun t => projectiveCoreAngle (β t)
  let rate := fun t => coreOriginalClockRate (β t)
  let x := fun t => k * ξ t 1
  let u := fun t => β t 1 * rate t
  let w₂ := fun t => β t 3 ^ 2 * rate t
  let wv := fun t => (β t 3 / (k * β t 2)) * rate t
  let xs := fun t => (|x t| / Real.cosh (θ t)) * rate t
  let xa := fun t => |x t| * rate t
  let A := fun t => (16 * Q) * u t + (8 * Q / k ^ 2) * w₂ t + (8 * Q) * wv t + 2 * xs t + (1 / k) * xa t
  have hk0 : 0 < k := by linarith only [hk]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ a ha)
  have hV (t : ℝ) (ht : t ∈ Icc a b) : 0 < β t 2 :=
    lt_of_lt_of_le zero_lt_one (hcore t ht).2.1
  have hflow (t : ℝ) (ht : t ∈ Icc a b) := hasDerivAt_projectiveOriginalFlow_time hD (hdom ht) (hA t ht)
  have hθ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt θ (rate t) t :=
    hasDerivAt_coreAngle_scaled (hflow t ht) (hV t ht)
  have hrate : ContinuousOn rate (Icc a b) := by
    intro t ht
    exact ((contDiffAt_coreOriginalClockRate 1 (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).1)).continuousAt.comp
        (hflow t ht).continuousAt).continuousWithinAt
  have hpos (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ rate t :=
    (coreRegion_clock_regular hk (hcore t ht)).2.2.le
  have hc (i : Fin 4) : ContinuousOn (fun t => β t i) (Icc a b) :=
    fun t ht => (hasDerivAt_pi.mp (hflow t ht) i).continuousAt.continuousWithinAt
  have hξ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt ξ
      (rate t • (coreAngleJacobian (θ t) (toCoreAngleState (β t))).mulVec (ξ t)) t :=
    hasDerivAt_coreProjectedFlowVariation hD (hdom ht) (hA t ht) (hV t ht)
      (ne_of_gt (coreRegion_clock_regular hk (hcore t ht)).2.1) w
  have hxc : ContinuousOn x (Icc a b) := fun t ht =>
    ((hasDerivAt_pi.mp (hξ t ht) 1).const_mul k).continuousAt.continuousWithinAt
  have hθc : ContinuousOn θ (Icc a b) := fun t ht => (hθ t ht).continuousAt.continuousWithinAt
  have hu : ContinuousOn u (Icc a b) := (hc 1).mul hrate
  have hw₂ : ContinuousOn w₂ (Icc a b) := ((hc 3).pow 2).mul hrate
  have hwv : ContinuousOn wv (Icc a b) :=
    ((hc 3).div (continuousOn_const.mul (hc 2)) (fun t ht => ne_of_gt (mul_pos hk0 (hV t ht)))).mul hrate
  have hxs : ContinuousOn xs (Icc a b) := (hxc.abs.div
    (Real.continuous_cosh.comp_continuousOn hθc) (fun t _ => ne_of_gt (Real.cosh_pos _))).mul hrate
  have hxa : ContinuousOn xa (Icc a b) := hxc.abs.mul hrate
  have hAc : ContinuousOn A (Icc a b) :=
    ((((hu.const_mul _).add (hw₂.const_mul _)).add (hwv.const_mul _)).add (hxs.const_mul _)).add (hxa.const_mul _)
  have hbound (t : ℝ) (ht : t ∈ Icc a b) :
      |rate t * (coreAngleJacobian (θ t) (toCoreAngleState (β t))).mulVec (ξ t) 0| ≤ A t := by
    have H := coreRegion_radius_variation_row hk (hcore t ht) (hQ t ht)
    dsimp only at H
    rw [coreWeightedJacobian_mulVec (ne_of_gt hk0)] at H
    have H' := mul_le_mul_of_nonneg_left H (hpos t ht)
    rw [abs_mul, abs_of_nonneg (hpos t ht)]
    convert! H' using 1
    dsimp [A, u, w₂, wv, xs, xa, x, scaleCoreVariation, θ]
    ring
  have hdiff := abs_sub_le_integral_bound hab
    (fun t ht => hasDerivAt_pi.mp (hξ t ht) 0) hAc hbound
  have hi₁ := (hu.const_mul (16 * Q)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₂ := (hw₂.const_mul (8 * Q / k ^ 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₃ := (hwv.const_mul (8 * Q)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₄ := (hxs.const_mul 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hi₅ := (hxa.const_mul (1 / k)).intervalIntegrable_of_Icc (μ := volume) hab
  have hlin : (∫ t in a..b, A t) =
      (16 * Q) * (∫ t in a..b, u t) + (8 * Q / k ^ 2) * (∫ t in a..b, w₂ t) +
        (8 * Q) * (∫ t in a..b, wv t) + 2 * (∫ t in a..b, xs t) + (1 / k) * (∫ t in a..b, xa t) := by
    dsimp only [A]
    rw [intervalIntegral.integral_add (((hi₁.add hi₂).add hi₃).add hi₄) hi₅,
      intervalIntegral.integral_add ((hi₁.add hi₂).add hi₃) hi₄,
      intervalIntegral.integral_add (hi₁.add hi₂) hi₃, intervalIntegral.integral_add hi₁ hi₂]
    simp only [intervalIntegral.integral_const_mul]
  obtain ⟨hUint, _, hWVint, hW₂int⟩ := projectiveOriginalFlow_core_weight_integrals hk hab hD hdom hA hcore
  obtain ⟨hXSint, hXAint⟩ := coreProjectedFlowVariation_strong_integrals hk hab hD hdom hA hcore hentry w hQ
  have hint := add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hUint (by positivity : 0 ≤ 16 * Q))
    (mul_le_mul_of_nonneg_left hW₂int (by positivity : 0 ≤ 8 * Q / k ^ 2)))
    (mul_le_mul_of_nonneg_left hWVint (by positivity : 0 ≤ 8 * Q)))
    (mul_le_mul_of_nonneg_left hXSint (by norm_num : (0 : ℝ) ≤ 2)))
    (mul_le_mul_of_nonneg_left hXAint (by positivity : 0 ≤ 1 / k))
  have hPk : β a 2 * β a 3 ≤ k := by
    have H := coreBootstrap_wall_bound hk (hcore a ha).2.2.2.2
    linarith only [H, hk]
  exact hdiff.trans (hlin.le.trans (hint.trans (core_radius_integral_constants hk
    (hcore a ha).2.2.1.1 (hcore a ha).2.2.2.1 hPk hQ0 (abs_nonneg _))))

theorem exists_large_core_radius_variation {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      ∀ v : CoreAngleState, ∀ t ∈ Icc 0 T,
        let w := fderiv ℝ coreRadiusEntry Y v
        let ξ := fun s => coreProjectedFlowVariation (coreRadiusEntry Y) 0 s w
        let Q := (2 * coreVariationBound) * (|v 0| + Y 0 * |v 1| + |v 2|)
        |ξ t 0 - ξ 0 0| ≤ 256 * (|Y 0 * ξ 0 1| / Y 0 ^ 2 + (Y 1 + Y 2) * Q / Y 0) := by
  have hD : 0 < projectiveStateDenom (coreRadiusEntry Y) :=
    (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hcore, _⟩ := exists_large_core_traversal hk hu hw
  obtain ⟨S, _, hfirstS, _, hnorm⟩ := exists_large_core_entry_variation hk hu hw
  have hST : S = T := hfirstS.unique hfirst
  subst S
  have hentry : Real.cosh (projectiveCoreAngle (projectiveOriginalFlow (coreRadiusEntry Y) 0 0)) = Y 0 := by
    rw [projectiveOriginalFlow_initial hD, projectiveCoreAngle,
      cosh_coreAngle (show 0 < coreRadiusEntry Y 2 by change (0 : ℝ) < 1; norm_num),
      coreRadius_coreRadiusEntry (by linarith only [hk] : 1 < Y 0)]
    exact div_one _
  refine ⟨T, hT, hfirst, ?_⟩
  intro v t ht w ξ Q
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have H := coreProjectedFlowVariation_radius_drift hk ht.1 hD
    (fun s hs => normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.1)
    (fun s hs => (hcore s (hsub hs)).1) (fun s hs => (hcore s (hsub hs)).2) hentry w
    (fun s hs => hnorm s (hsub hs) v)
  dsimp only at H
  rw [projectiveOriginalFlow_initial hD] at H
  simpa only [show coreRadiusEntry Y 1 = Y 1 from rfl, show coreRadiusEntry Y 2 = 1 from rfl,
    show coreRadiusEntry Y 3 = Y 2 from rfl, one_mul] using H

end BianchiIX
