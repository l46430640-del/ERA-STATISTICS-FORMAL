import BianchiIX.Dynamics.ExitClockLogMultiplier

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem exitClockLogMultiplier_direction_integral {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hs : 0 ≤ s) (i : Fin 2)
    (H : ∀ r ∈ Icc 0 s, ContDiffAt ℝ 1 (exitClockRateIntegrand I i) (Y, r)) (v : ExitTailState) :
    fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y v =
      ∫ r in (0 : ℝ)..s, fderiv ℝ (exitClockRateIntegrand I i) (Y, r) (v, 0) := by
  rw [(exitClockLogMultiplier_regular hs i H).2]
  have HC : ContinuousOn (fun r => (fderiv ℝ (exitClockRateIntegrand I i) (Y, r)).comp
      (ContinuousLinearMap.inl ℝ ExitTailState ℝ)) (Icc 0 s) := fun r hr =>
    ((((H r hr).continuousAt_fderiv (by norm_num)).clm_comp continuousAt_const).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  exact ContinuousLinearMap.intervalIntegral_apply (HC.intervalIntegrable_of_Icc hs) v

theorem exitClockLogMultiplier_weak_bound {I : Set ℝ} {Y : ExitTailState} {s K b : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hb : 0 ≤ b)
    (hΦ : ∀ r ∈ Icc 0 s, ContDiffAt ℝ 1 (exitClockFlow I) (Y, r))
    (hreg : ∀ r ∈ Icc 0 s, (7 / 4 ≤ exitClockFlow I (Y, r) 0 ∧ exitClockFlow I (Y, r) 0 ≤ 17 / 4) ∧
      |exitClockFlow I (Y, r) 1| ≤ 1 / 100 ∧ |exitClockFlow I (Y, r) 2| ≤ 1 / 100)
    (hnorm : ∀ r ∈ Icc 0 s, ‖fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y‖ ≤ K)
    (hamp : ∀ r ∈ Icc 0 s, |exitClockFlow I (Y, r) 1| + |exitClockFlow I (Y, r) 2| ≤ K * b)
    (hrad : ∀ r ∈ Icc 0 s, |fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y (Pi.single 2 1) 0| ≤
      K * b * (1 + r)) (i : Fin 2) :
    |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y (Pi.single 2 1)| ≤
      1024 * K ^ 2 * (1 + b * s * (1 + s)) := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hKK : K ≤ K ^ 2 := by nlinarith only [hK]
  have hv (r : ℝ) (hr : r ∈ Icc 0 s) : 0 ≤ Real.exp (-r) ∧ Real.exp (-r) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.1)⟩
  have hsep (r : ℝ) (hr : r ∈ Icc 0 s) : (Real.exp (-r)) ^ 2 < (exitClockFlow I (Y, r) 0) ^ 2 := by
    nlinarith only [(hreg r hr).1.1, (hv r hr).1, (hv r hr).2]
  have hd (r : ℝ) (hr : r ∈ Icc 0 s) : exitTailSpeed (exitClockFlow I (Y, r) 0)
      (exitClockFlow I (Y, r) 1) (Real.exp (-r)) (exitClockFlow I (Y, r) 2) ≠ 0 := by
    have H := exitTailSpeed_compact (hreg r hr).1.1 (hreg r hr).2.1 (hv r hr) (hreg r hr).2.2
    linarith only [H]
  rw [exitClockLogMultiplier_direction_integral hs i
    (fun r hr => contDiffAt_exitClockRateIntegrand (hΦ r hr) (hsep r hr) (hd r hr) i)]
  let B := 1024 * K ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have HE (r : ℝ) (hr : r ∈ Icc 0 s) :
      |fderiv ℝ (exitClockRateIntegrand I i) (Y, r) (Pi.single 2 1, 0)| ≤
        B * b * (1 + s) + B * Real.exp (-r) + 0 * Real.exp (-2 * r) := by
    rw [exitClockRateIntegrand_partial (hΦ r hr) (hsep r hr) (hd r hr) i]
    let ξ := fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y (Pi.single 2 1)
    have hξ (j : Fin 3) : |ξ j| ≤ K := by
      have H := (norm_le_pi_norm ξ j).trans
        (((fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y).le_opNorm (Pi.single 2 1)).trans
          (mul_le_mul_of_nonneg_right (hnorm r hr) (norm_nonneg _)))
      simpa only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using H
    have HG := exitTailWallRate_direction_bound (hreg r hr).1 (hreg r hr).2.1 (hv r hr) (hreg r hr).2.2 ξ i
    have Hp : 0 ≤ Real.exp (-r) + K * b := by positivity
    have HM : 256 * (Real.exp (-r) + |exitClockFlow I (Y, r) 1| + |exitClockFlow I (Y, r) 2|) * (|ξ 1| + |ξ 2|) ≤
        512 * K * (Real.exp (-r) + K * b) := by
      calc
        _ = 256 * (Real.exp (-r) + (|exitClockFlow I (Y, r) 1| + |exitClockFlow I (Y, r) 2|)) * (|ξ 1| + |ξ 2|) := by ring
        _ ≤ 256 * (Real.exp (-r) + K * b) * (K + K) := by
          gcongr
          · exact hamp r hr
          · exact hξ 1
          · exact hξ 2
        _ = _ := by ring
    have Hrad := hrad r hr
    have hr0 : 0 ≤ r := hr.1
    dsimp only [B]
    nlinarith only [HG, HM, Hrad,
      mul_le_mul_of_nonneg_right hKK (by positivity : 0 ≤ b * (1 + r)),
      mul_le_mul_of_nonneg_left hr.2 (by positivity : 0 ≤ K ^ 2 * b),
      mul_le_mul_of_nonneg_right hKK (Real.exp_pos (-r)).le,
      mul_nonneg (by positivity : 0 ≤ K ^ 2 * b) hr0,
      mul_nonneg (sq_nonneg K) (Real.exp_pos (-r)).le]
  have HI := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (f := fun r => fderiv ℝ (exitClockRateIntegrand I i) (Y, r) (Pi.single 2 1, 0))
    (g := fun r => B * b * (1 + s) + B * Real.exp (-r) + 0 * Real.exp (-2 * r)) hs
    (ae_of_all volume fun r hr => by simpa only [Real.norm_eq_abs] using HE r ⟨hr.1.le, hr.2⟩)
    ((by fun_prop : Continuous (fun r => B * b * (1 + s) + B * Real.exp (-r) + 0 * Real.exp (-2 * r))).intervalIntegrable 0 s)
  have HB := integral_exit_tail_envelope (T := s) (A := B * b * (1 + s)) hB (by norm_num : (0 : ℝ) ≤ 0)
  exact (show _ ≤ _ from HI).trans (HB.trans_eq (by dsimp only [B]; ring))

end BianchiIX
