import BianchiIX.Dynamics.EntranceWallLogBounds
import BianchiIX.Dynamics.EntranceReturnSegment
import BianchiIX.Analysis.ScalarMultiplier

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem entranceWeakLogRate_error {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    |entranceWeakLogRate y + 1| ≤ 8 / k := by
  have hk0 : 0 < k := by linarith only [hk]
  have hD := entranceRegion_clock_pos hk hy
  have hDlo : k / 2 ≤ entranceClockRate y := by linarith only [hk, (entranceRegion_speed hk hy).1]
  have hc := (entranceWallLogRates_base_bounds hk hy).1
  change |-1 - 2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y + 1| ≤ _
  rw [show -1 - 2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y + 1 =
    -(2 * (1 + coupling (y 1) (y 2) (y 3)) / entranceClockRate y) by ring,
    abs_neg, abs_div, abs_mul, abs_of_pos hD, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (div_le_div_iff₀ hD hk0).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hc hk0.le, hDlo]

/-- The active-weak product has an error exponent controlled by the logarithmic flight length. -/
theorem scaled_entrance_weak_product_bound {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    let E := ∫ r in s..t, -2 * a r * (1 + coupling (Y r 1) (Y r 2) (Y r 3))
    Y t 2 * Y t 3 = Y s 2 * Y s 3 * Real.exp E ∧
      |E| ≤ 8 / k * (Real.log (Y t 2) - Real.log (Y s 2)) := by
  intro E
  let b := fun r => -2 * a r * (1 + coupling (Y r 1) (Y r 2) (Y r 3))
  let q := fun r => a r * entranceClockRate (Y r)
  have hcoord (i : Fin 4) := (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hbc : ContinuousOn b (Icc s t) := by
    dsimp only [b]
    apply (hac.const_mul (-2)).mul
    unfold coupling
    fun_prop
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hp (r : ℝ) (hr : r ∈ Ioo s t) :
      HasDerivAt (fun u => Y u 2 * Y u 3) (b r * (Y r 2 * Y r 3)) r := by
    have H := (hasDerivAt_pi.mp (hY r (Ioo_subset_Icc_self hr)) 2).mul
      (hasDerivAt_pi.mp (hY r (Ioo_subset_Icc_self hr)) 3)
    convert! H using 1
    dsimp [b, projectiveField, activeVelocity, weakVelocity]
    ring
  refine ⟨homogeneous_solution_eq_exp_integral_Icc hst hbc ((hcoord 2).mul (hcoord 3)) hp, ?_⟩
  have hb (r : ℝ) (hr : r ∈ Icc s t) : |b r| ≤ (8 / k) * q r := by
    have hD := entranceRegion_clock_pos hk (hy r hr)
    have heq : b r = q r * (entranceWeakLogRate (Y r) + 1) := by
      dsimp only [b, q, entranceWeakLogRate, connectionWeakClockRate]
      change _ = (a r * entranceClockRate (Y r)) * (-1 - 2 * (1 + coupling _ _ _) / entranceClockRate (Y r) + 1)
      field_simp
      ring
    rw [heq, abs_mul, abs_of_nonneg (mul_nonneg (ha r hr) hD.le)]
    exact (mul_le_mul_of_nonneg_left (entranceWeakLogRate_error hk (hy r hr))
      (mul_nonneg (ha r hr) hD.le)).trans_eq (mul_comm _ _)
  have hbound := intervalIntegral.integral_mono_on (μ := volume) hst
    (hbc.abs.intervalIntegrable_of_Icc hst) ((hqc.const_mul (8 / k)).intervalIntegrable_of_Icc hst) hb
  have hz (r : ℝ) (hr : r ∈ Icc s t) := hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hqeq : (∫ r in s..t, q r) = Real.log (Y t 2) - Real.log (Y s 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r hr => hz r (uIcc_of_le hst ▸ hr))
      (hqc.intervalIntegrable_of_Icc hst)
  have HE := (intervalIntegral.abs_integral_le_integral_abs (f := b) hst).trans hbound
  rwa [intervalIntegral.integral_const_mul, hqeq] at HE

def entranceWeakProductExponent (y : ProjectiveState) : ℝ :=
  ∫ t in 0..entranceReturnTime y,
    -2 * normalizedProjectiveRate (fromProjectiveState y) 0 t *
      (1 + coupling (projectiveOriginalFlow y 0 t 1) (projectiveOriginalFlow y 0 t 2)
        (projectiveOriginalFlow y 0 t 3))

theorem entranceReturn_weak_product_bound {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 3 = y 2 * y 3 * Real.exp (entranceWeakProductExponent y) ∧
      |entranceWeakProductExponent y| ≤ 8 * (-Real.log (y 2)) / coreRadius (y 0) (y 2) := by
  let x := fromProjectiveState y
  let Y := projectiveOriginalFlow y 0
  let a := normalizedProjectiveRate x 0
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have H := (entranceReturn_regular hk hm hu hv hw).1
  have ht : 0 ≤ entranceReturnTime y := H.1.1.1.le
  have hinit : Y 0 = y := projectiveOriginalFlow_initial hD 0
  have hA (r : ℝ) (hr : r ∈ Icc 0 (entranceReturnTime y)) : 0 < a r := (H.2.1 r hr).2
  have hY (r : ℝ) (hr : r ∈ Icc 0 (entranceReturnTime y)) :
      HasDerivAt Y (a r • projectiveField (Y r)) r :=
    hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (H.2.1 r hr).1)
      (hA r hr).ne' ((normalizedMaxCurve_constraint (H.2.1 r hr).1).trans
        (fromProjectiveState_constraint hD.ne'))
  have hV (r : ℝ) (hr : r ∈ Icc 0 (entranceReturnTime y)) : 0 < Y r 2 := by
    apply normalized_projective_wall_pos (H.2.1 0 ⟨le_rfl, ht⟩).1 (H.2.1 r hr).1
      (hA 0 ⟨le_rfl, ht⟩) (hA r hr) 1
    change 0 < Y 0 2
    rw [hinit]
    exact hv.1
  have hac : ContinuousOn a (Icc 0 (entranceReturnTime y)) :=
    (continuousOn_normalizedProjectiveRate x 0).mono (fun r hr => (H.2.1 r hr).1)
  have HE := scaled_entrance_weak_product_bound hk ht hY hac (fun r hr => (hA r hr).le)
    (entranceReturn_region hk hm hu hv hw) hV
  change entranceReturnState y 2 * entranceReturnState y 3 = Y 0 2 * Y 0 3 * Real.exp (entranceWeakProductExponent y) ∧
    |entranceWeakProductExponent y| ≤ 8 / coreRadius (y 0) (y 2) *
      (Real.log (entranceReturnState y 2) - Real.log (Y 0 2)) at HE
  rw [hinit, (entranceReturn_active_component hk hm hu hv hw).1, one_mul, Real.log_one, zero_sub] at HE
  exact ⟨HE.1, HE.2.trans_eq (by ring)⟩

end BianchiIX
