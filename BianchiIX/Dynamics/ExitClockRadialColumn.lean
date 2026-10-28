import BianchiIX.Dynamics.ExitClockWallFactor
import BianchiIX.Analysis.ExitRadialColumnBounds

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem exitClock_radial_column_bound {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T s K b : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) (hK : 1 ≤ K)
    (hb : |Y 1| + |Y 2| ≤ b)
    (hreg : ∀ r ∈ Icc 0 s, (7 / 4 ≤ exitClockFlow I (Y, r) 0 ∧ exitClockFlow I (Y, r) 0 ≤ 17 / 4) ∧
      |exitClockFlow I (Y, r) 1| ≤ 1 / 100 ∧ |exitClockFlow I (Y, r) 2| ≤ 1 / 100)
    (hbound : ∀ r ∈ Icc 0 s, ‖fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y‖ ≤ K)
    (hmult : ∀ r ∈ Icc 0 s, ∀ i : Fin 2, Real.exp (exitClockLogMultiplier I i Y r) ≤ K ∧
      ‖fderiv ℝ (fun Z => exitClockLogMultiplier I i Z r) Y‖ ≤ K * r)
    (v : ExitTailState) (hv : v 1 = 0) :
    |fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y v 0 - v 0| ≤
      512 * K ^ 3 * ((2 * |Y 1| + b ^ 2 * s * (1 + s)) * ‖v‖ + b * |v 2| * s) := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hb0 : 0 ≤ b := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hb
  have ha : |Y 1| ≤ b := le_trans (le_add_of_nonneg_right (abs_nonneg _)) hb
  let β : ℝ → ExitTailState := fun r => exitClockFlow I (Y, r)
  let ξ : ℝ → ExitTailState := fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0)
  have hsub (r : ℝ) (hr : r ∈ Icc 0 s) : r ∈ Icc 0 (exitEntryClock (Y, T)) := ⟨hr.1, hr.2.trans hs.2⟩
  have HF (r : ℝ) (hr : r ∈ Icc 0 s) := exitClockFlow_on_interval hIo hI hUo hY H hT hcover (hsub r hr)
  have heq (r : ℝ) (hr : r ∈ Icc 0 s) :
      fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y v = ξ r :=
    fderiv_parameterSlice_apply ((HF r hr).1.differentiableAt (by norm_num)) v
  have hξ (r : ℝ) (hr : r ∈ Icc 0 s) :
      HasDerivAt ξ (fderiv ℝ (exitTailField (Real.exp (-r))) (β r) (ξ r)) r := (HF r hr).2.2 v
  have hξ0 : ξ 0 = v := exitClockFlow_variation_initial hIo hI hUo hY H (hcover ⟨le_rfl, hT⟩) v
  have henvelope (r : ℝ) (hr : r ∈ Icc 0 s) :
      |fderiv ℝ (exitTailField (Real.exp (-r))) (β r) (ξ r) 0| ≤
        512 * K ^ 3 * ((|Y 1| * (1 + r) * Real.exp (-r) + b ^ 2 * (1 + r)) * ‖v‖ + b * |v 2|) := by
    have hr0 : 0 ≤ r := hr.1
    have hfac (i : Fin 2) : β r i.succ = Y i.succ * Real.exp (exitClockLogMultiplier I i Y r) :=
      (exitClockFlow_eventually_wall_factor hIo hI hUo hY H hT hcover (hsub r hr) i).self_of_nhds
    have hamp (i : Fin 2) : |β r i.succ| ≤ K * |Y i.succ| := by
      rw [hfac i, abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith only [mul_le_mul_of_nonneg_left (hmult r hr i).1 (abs_nonneg (Y i.succ))]
    have hsum : |β r 1| + |β r 2| ≤ K * b := by
      have h0 : |β r 1| ≤ K * |Y 1| := hamp 0
      have h1 : |β r 2| ≤ K * |Y 2| := hamp 1
      nlinarith only [h0, h1, mul_le_mul_of_nonneg_left hb hK0]
    have hlog (i : Fin 2) : |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z r) Y v| ≤ K * r * ‖v‖ :=
      ((fderiv ℝ (fun Z => exitClockLogMultiplier I i Z r) Y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hmult r hr i).2 (norm_nonneg v))
    have hwvar (i : Fin 2) : |ξ r i.succ| ≤ K * |v i.succ| + K ^ 2 * |Y i.succ| * r * ‖v‖ := by
      have HD := exitClockFlow_wall_differential hIo hI hUo hY H hT hcover (hsub r hr) i v
      rw [heq r hr] at HD
      rw [HD]
      have HA := abs_add_le (Real.exp (exitClockLogMultiplier I i Y r) * v i.succ)
        (β r i.succ * fderiv ℝ (fun Z => exitClockLogMultiplier I i Z r) Y v)
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)] at HA
      have HB := mul_le_mul (hamp i) (hlog i) (abs_nonneg _) (mul_nonneg hK0 (abs_nonneg _))
      nlinarith only [HA, HB, mul_le_mul_of_nonneg_right (hmult r hr i).1 (abs_nonneg (v i.succ))]
    have hv0 : |ξ r 0| ≤ K * ‖v‖ := by
      have HN := ((fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hbound r hr) (norm_nonneg v))
      rw [heq r hr] at HN
      exact (show |ξ r 0| ≤ ‖ξ r‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (ξ r) 0).trans HN
    have hv1 : |ξ r 1| ≤ K ^ 2 * |Y 1| * r * ‖v‖ := by
      have HV : |ξ r 1| ≤ K * |v 1| + K ^ 2 * |Y 1| * r * ‖v‖ := hwvar 0
      simpa only [hv, abs_zero, mul_zero, zero_add] using HV
    have hv2 : |ξ r 2| ≤ K * |v 2| + K ^ 2 * b * r * ‖v‖ := by
      have HV : |ξ r 2| ≤ K * |v 2| + K ^ 2 * |Y 2| * r * ‖v‖ := hwvar 1
      apply HV.trans
      gcongr
      linarith only [hb, abs_nonneg (Y 1)]
    exact exitTail_radial_column_envelope hK (abs_nonneg _) ha hr.1 (norm_nonneg _) (abs_nonneg _)
      (hreg r hr).1 (hreg r hr).2.1 ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.1)⟩
      (hreg r hr).2.2 (hamp 0) hsum hv0 hv1 hv2
  have HB := abs_sub_le_integral_bound hs.1 (fun r hr => hasDerivAt_pi.mp (hξ r hr) 0)
    (B := fun r => 512 * K ^ 3 * ((|Y 1| * (1 + r) * Real.exp (-r) + b ^ 2 * (1 + r)) * ‖v‖ + b * |v 2|))
    (by fun_prop) henvelope
  rw [intervalIntegral.integral_const_mul, hξ0] at HB
  rw [heq s ⟨hs.1, le_rfl⟩]
  exact HB.trans (mul_le_mul_of_nonneg_left
    (integral_exit_radial_column_envelope hs.1 (abs_nonneg _) (norm_nonneg _)) (by positivity))

end BianchiIX
