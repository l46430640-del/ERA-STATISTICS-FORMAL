import BianchiIX.Dynamics.EntrancePhaseActiveSource
import BianchiIX.Dynamics.EntranceProductMoments
import BianchiIX.Dynamics.EntranceWallBudgets
import BianchiIX.Dynamics.EntranceReturnSegment

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem exists_scaled_entrance_phase_active_budget :
    ∃ C > (0 : ℝ), ∀ (Y : ℝ → ProjectiveState) (a : ℝ → ℝ) (s t k : ℝ),
      7 / 4 ≤ k → s ≤ t →
      (∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r) →
      ContinuousOn a (Icc s t) → (∀ r ∈ Icc s t, 0 ≤ a r) →
      (∀ r ∈ Icc s t, entranceRegion k (Y r)) → (∀ r ∈ Icc s t, 0 < Y r 2) →
      k * (Y s 1 + Y s 3) ^ 2 ≤ 1 →
      (∫ r in s..t, |entrancePhaseActiveSource (Y r)| * (a r * entranceClockRate (Y r))) ≤
        C * (Y s 1 * Y s 2 + (Y s 2 * Y s 3) ^ 2 / k ^ 2) / k := by
  obtain ⟨K, hK, HK⟩ := exists_entrancePhaseActiveSource_bound
  refine ⟨3 * K, by positivity, ?_⟩
  intro Y a s t k hk hst hY hac ha hy hv hsmall
  let q := fun r => a r * entranceClockRate (Y r)
  let P := fun r => Y r 1 * Y r 2 * q r
  let W := fun r => (Y r 2 * Y r 3) ^ 2 * q r
  have hk0 : 0 < k := by linarith
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hcoord (i : Fin 4) := (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hPc : ContinuousOn P (Icc s t) := ((hcoord 1).mul (hcoord 2)).mul hqc
  have hWc : ContinuousOn W (Icc s t) := (((hcoord 2).mul (hcoord 3)).pow 2).mul hqc
  have hSc : ContinuousOn (fun r => |entrancePhaseActiveSource (Y r)| * q r) (Icc s t) := by
    apply ContinuousOn.mul ?_ hqc
    intro r hr
    exact (((continuousAt_entrancePhaseActiveSource hk (hy r hr) (hv r hr)).comp
      (hY r hr).continuousAt).abs).continuousWithinAt
  have hwall := (scaled_entrance_wall_budgets hk hst hY hac ha hy hv).1
  have hbound (r : ℝ) (hr : r ∈ Icc s t) :
      |entrancePhaseActiveSource (Y r)| * q r ≤ K * P r + (K / k ^ 4) * W r := by
    have hb : k * (Y r 1 + Y r 3) ^ 2 ≤ 1 := by
      have H := (sq_le_sq₀ (add_nonneg (hy r hr).2.2.1.1 (hy r hr).2.2.2.2.1)
        (add_nonneg (hy s hs).2.2.1.1 (hy s hs).2.2.2.2.1)).mpr
        (add_le_add (hwall r hr).1 (hwall r hr).2)
      exact (mul_le_mul_of_nonneg_left H hk0.le).trans hsmall
    exact (mul_le_mul_of_nonneg_right (HK k (Y r) hk (hy r hr) (hv r hr) hb) (hq r hr)).trans_eq
      (by dsimp [P, W]; ring)
  have HI := intervalIntegral.integral_mono_on (μ := volume) hst (hSc.intervalIntegrable_of_Icc hst)
    (((hPc.const_mul K).add (hWc.const_mul (K / k ^ 4))).intervalIntegrable_of_Icc hst) hbound
  simp only [Pi.add_apply] at HI
  rw [intervalIntegral.integral_add ((hPc.const_mul K).intervalIntegrable_of_Icc hst)
    ((hWc.const_mul (K / k ^ 4)).intervalIntegrable_of_Icc hst),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at HI
  obtain ⟨HP, _, HW, _⟩ := scaled_entrance_product_moments hk hst hY hac ha hy hv
  apply HI.trans ((add_le_add (mul_le_mul_of_nonneg_left HP hK.le)
    (mul_le_mul_of_nonneg_left HW (show 0 ≤ K / k ^ 4 by positivity))).trans ?_)
  have Hweak : (Y s 2 * Y s 3) ^ 2 / 2 ≤ 3 * (Y s 2 * Y s 3) ^ 2 := by
    nlinarith only [sq_nonneg (Y s 2 * Y s 3)]
  calc
    _ = 3 * K * (Y s 1 * Y s 2) / k + (K / k ^ 3) * ((Y s 2 * Y s 3) ^ 2 / 2) := by field_simp
    _ ≤ 3 * K * (Y s 1 * Y s 2) / k + (K / k ^ 3) * (3 * (Y s 2 * Y s 3) ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left Hweak (by positivity))
    _ = _ := by field_simp

theorem exists_entrance_return_phase_active_budget :
    ∃ C > (0 : ℝ), ∀ (y : ProjectiveState),
      7 / 4 ≤ coreRadius (y 0) (y 2) → 1 ≤ y 0 →
      (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) →
      coreRadius (y 0) (y 2) * (y 1 + y 3) ^ 2 ≤ 1 →
      let k := coreRadius (y 0) (y 2)
      let Y := projectiveOriginalFlow y 0
      (∫ r in (0 : ℝ)..entranceReturnTime y, |entrancePhaseActiveSource (Y r)| *
        (normalizedProjectiveRate (fromProjectiveState y) 0 r * entranceClockRate (Y r))) ≤
          C * (y 1 * y 2 + (y 2 * y 3) ^ 2 / k ^ 2) / k := by
  obtain ⟨C, hC, HC⟩ := exists_scaled_entrance_phase_active_budget
  refine ⟨C, hC, ?_⟩
  intro y hk hm hu hv hw hsmall k Y
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
  have H := HC Y a 0 T k hk ht hY hac (fun r hr => (HR.2.1 r hr).2.le)
    (entranceReturn_region hk hm hu hv hw) hvY (by simpa only [hinit] using hsmall)
  simpa only [hinit] using H

end BianchiIX
