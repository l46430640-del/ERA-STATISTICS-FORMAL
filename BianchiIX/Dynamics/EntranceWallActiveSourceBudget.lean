import BianchiIX.Dynamics.EntranceActiveLogRates
import BianchiIX.Dynamics.EntranceActiveSourceMoments
import BianchiIX.Dynamics.EntranceReturnSegment

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The integrated amplitude forcing costs only one inverse power, uniformly in residence time. -/
theorem scaled_entrance_wall_active_source_budget {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2)
    (hsmall : k ^ 2 * (Y s 1 + Y s 3) ≤ 1) :
    (∫ r in s..t, ‖entranceWallActiveSource k (Y r)‖ * (a r * entranceClockRate (Y r))) ≤ 1536 / k := by
  let q := fun r => a r * entranceClockRate (Y r)
  let E := fun r => (Y r 2) ^ 2 * q r
  let P := fun r => Y r 1 * Y r 2 * q r
  let W := fun r => Y r 2 * Y r 3 * q r
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hu0 := (hy s hs).2.2.1.1
  have hw0 := (hy s hs).2.2.2.2.1
  have hv0 := (hv s hs).le
  have hv1 := (hy s hs).2.2.2.1.2
  have hcoord (i : Fin 4) := (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hEc : ContinuousOn E (Icc s t) := ((hcoord 2).pow 2).mul hqc
  have hPc : ContinuousOn P (Icc s t) := ((hcoord 1).mul (hcoord 2)).mul hqc
  have hWc : ContinuousOn W (Icc s t) := ((hcoord 2).mul (hcoord 3)).mul hqc
  have hEPc : ContinuousOn (fun r => (192 / k) * E r + (192 * (1 + k)) * P r) (Icc s t) :=
    (hEc.const_mul _).add (hPc.const_mul _)
  have hSc : ContinuousOn (fun r => ‖entranceWallActiveSource k (Y r)‖ * q r) (Icc s t) := by
    apply ContinuousOn.mul ?_ hqc
    intro r hr
    exact (((continuousAt_entranceWallActiveSource hk (hy r hr) (hv r hr)).comp
      (hY r hr).continuousAt).norm).continuousWithinAt
  have hbound (r : ℝ) (hr : r ∈ Icc s t) :
      ‖entranceWallActiveSource k (Y r)‖ * q r ≤ (192 / k) * E r + (192 * (1 + k)) * P r + 192 * W r := by
    exact (mul_le_mul_of_nonneg_right (entranceWallActiveSource_bound hk (hy r hr) (hv r hr)) (hq r hr)).trans_eq
      (by dsimp [E, P, W]; ring)
  have HI := intervalIntegral.integral_mono_on (μ := volume) hst (hSc.intervalIntegrable_of_Icc hst)
    ((hEPc.add (hWc.const_mul 192)).intervalIntegrable_of_Icc hst) hbound
  simp only [Pi.add_apply] at HI
  rw [intervalIntegral.integral_add (hEPc.intervalIntegrable_of_Icc hst)
      ((hWc.const_mul 192).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_add ((hEc.const_mul (192 / k)).intervalIntegrable_of_Icc hst)
      ((hPc.const_mul (192 * (1 + k))).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at HI
  obtain ⟨_, HE, HW⟩ := scaled_entrance_active_source_moments hk hst hY hac ha hy hv
  have HP := (scaled_entrance_product_moments hk hst hY hac ha hy hv).1
  have Hsum := add_le_add (add_le_add (mul_le_mul_of_nonneg_left HE (show 0 ≤ 192 / k by positivity))
    (mul_le_mul_of_nonneg_left HP (show 0 ≤ 192 * (1 + k) by positivity)))
    (mul_le_mul_of_nonneg_left HW (by norm_num : (0 : ℝ) ≤ 192))
  have hu : Y s 1 ≤ 1 / k := (le_div_iff₀ hk0).mpr (by
    have H := mul_le_mul_of_nonneg_right hk1 (mul_nonneg hk0.le hu0)
    nlinarith only [H, hsmall, mul_nonneg (sq_nonneg k) hw0])
  have huv : Y s 1 * Y s 2 ≤ 1 / k := (mul_le_of_le_one_right hu0 hv1).trans hu
  have huvdiv : Y s 1 * Y s 2 / k ≤ 1 / k := (div_le_self (mul_nonneg hu0 hv0) hk1).trans huv
  have hkw : k * (Y s 2 * Y s 3) ≤ 1 / k := (le_div_iff₀ hk0).mpr (by
    have H := mul_le_mul_of_nonneg_right hv1 (mul_nonneg (sq_nonneg k) hw0)
    nlinarith only [H, hsmall, mul_nonneg (sq_nonneg k) hu0])
  have Hbudget : 1 / (2 * k) + 3 * (Y s 1 * Y s 2 / k) + 3 * (Y s 1 * Y s 2) + k * (Y s 2 * Y s 3) ≤ 8 / k := by
    rw [show 1 / (2 * k) = (1 / k) / 2 by ring, show 8 / k = 8 * (1 / k) by ring]
    linarith only [huv, huvdiv, hkw, (one_div_pos.mpr hk0)]
  apply HI.trans (Hsum.trans ?_)
  calc
    _ = 192 * (1 / (2 * k) + 3 * (Y s 1 * Y s 2 / k) + 3 * (Y s 1 * Y s 2) + k * (Y s 2 * Y s 3)) := by
      field_simp; ring
    _ ≤ 192 * (8 / k) := mul_le_mul_of_nonneg_left Hbudget (by norm_num)
    _ = _ := by ring

theorem entrance_return_wall_active_source_budget {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000)
    (hsmall : coreRadius (y 0) (y 2) ^ 2 * (y 1 + y 3) ≤ 1) :
    let k := coreRadius (y 0) (y 2)
    let Y := projectiveOriginalFlow y 0
    (∫ r in (0 : ℝ)..entranceReturnTime y, ‖entranceWallActiveSource k (Y r)‖ *
      (normalizedProjectiveRate (fromProjectiveState y) 0 r * entranceClockRate (Y r))) ≤ 1536 / k := by
  intro k Y
  let x := fromProjectiveState y
  let a := normalizedProjectiveRate x 0
  let T := entranceReturnTime y
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint hD.ne'
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have ht : 0 ≤ T := HR.1.1.1.le
  have hinit : Y 0 = y := projectiveOriginalFlow_initial hD 0
  have hY (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivAt Y (a r • projectiveField (Y r)) r :=
    hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (HR.2.1 r hr).1)
      (HR.2.1 r hr).2.ne' ((normalizedMaxCurve_constraint (HR.2.1 r hr).1).trans hc)
  have hac : ContinuousOn a (Icc 0 T) :=
    (continuousOn_normalizedProjectiveRate x 0).mono (fun r hr => (HR.2.1 r hr).1)
  have hvY (r : ℝ) (hr : r ∈ Icc 0 T) : 0 < Y r 2 := by
    apply normalized_projective_wall_pos (HR.2.1 0 ⟨le_rfl, ht⟩).1 (HR.2.1 r hr).1
      (HR.2.1 0 ⟨le_rfl, ht⟩).2 (HR.2.1 r hr).2 1
    change 0 < Y 0 2
    simpa only [hinit] using hv.1
  exact scaled_entrance_wall_active_source_budget hk ht hY hac (fun r hr => (HR.2.1 r hr).2.le)
    (entranceReturn_region hk hm hu hv hw) hvY (by simpa only [hinit] using hsmall)

end BianchiIX
