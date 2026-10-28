import BianchiIX.Dynamics.ExitClockBounds
import BianchiIX.Analysis.ExitTailRateBounds
import BianchiIX.Analysis.CompactIntegralRegularity

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def exitClockRateIntegrand (I : Set ℝ) (i : Fin 2) (p : ExitTailState × ℝ) : ℝ :=
  exitTailWallRate (Real.exp (-p.2)) (exitClockFlow I p) i

def exitClockLogMultiplier (I : Set ℝ) (i : Fin 2) (Y : ExitTailState) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..s, exitClockRateIntegrand I i (Y, r)

theorem exitClockLogMultiplier_eq_log (I : Set ℝ) (i : Fin 2) (Y : ExitTailState) (s : ℝ) :
    exitClockLogMultiplier I i Y s =
      Real.log (exitTailMultiplier (fun r => exitClockFlow I (Y, r)) i s) :=
  (Real.log_exp _).symm

theorem contDiffAt_exitClockRateIntegrand {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hΦ : ContDiffAt ℝ 1 (exitClockFlow I) (Y, s))
    (hv : (Real.exp (-s)) ^ 2 < (exitClockFlow I (Y, s) 0) ^ 2)
    (hd : exitTailSpeed (exitClockFlow I (Y, s) 0) (exitClockFlow I (Y, s) 1)
      (Real.exp (-s)) (exitClockFlow I (Y, s) 2) ≠ 0) (i : Fin 2) :
    ContDiffAt ℝ 1 (exitClockRateIntegrand I i) (Y, s) := by
  have hmap : ContDiffAt ℝ 1 (fun p : ExitTailState × ℝ => (Real.exp (-p.2), exitClockFlow I p)) (Y, s) :=
    (contDiffAt_snd.neg.exp).prodMk hΦ
  have HR := (contDiffAt_exitTailWallRate 1 hv hd).comp (Y, s) hmap
  exact contDiffAt_pi.mp HR i

theorem exitClockRateIntegrand_partial {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hΦ : ContDiffAt ℝ 1 (exitClockFlow I) (Y, s))
    (hv : (Real.exp (-s)) ^ 2 < (exitClockFlow I (Y, s) 0) ^ 2)
    (hd : exitTailSpeed (exitClockFlow I (Y, s) 0) (exitClockFlow I (Y, s) 1)
      (Real.exp (-s)) (exitClockFlow I (Y, s) 2) ≠ 0) (i : Fin 2) (v : ExitTailState) :
    fderiv ℝ (exitClockRateIntegrand I i) (Y, s) (v, 0) =
      fderiv ℝ (exitTailWallRate (Real.exp (-s))) (exitClockFlow I (Y, s))
        (fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y v) i := by
  have hFs : HasFDerivAt (fun Z => exitClockFlow I (Z, s))
      (fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y) Y := by
    have HF := hΦ.comp Y (contDiffAt_id.prodMk (contDiffAt_const (c := s)))
    exact (HF.differentiableAt (by norm_num)).hasFDerivAt
  have hAs : ContDiffAt ℝ 1 (exitTailWallRate (Real.exp (-s))) (exitClockFlow I (Y, s)) := by
    have HA := (contDiffAt_exitTailWallRate 1 hv hd).comp (exitClockFlow I (Y, s))
      ((contDiffAt_const (c := Real.exp (-s))).prodMk contDiffAt_id)
    exact HA
  have HA := (hasFDerivAt_pi'.mp (hAs.differentiableAt (by norm_num)).hasFDerivAt i).comp Y hFs
  have HP := ((contDiffAt_exitClockRateIntegrand hΦ hv hd i).differentiableAt
    (by norm_num)).hasFDerivAt.comp Y (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y s)
  exact congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v) (HP.unique HA)

theorem exitClockLogMultiplier_regular {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hs : 0 ≤ s) (i : Fin 2)
    (H : ∀ r ∈ Icc 0 s, ContDiffAt ℝ 1 (exitClockRateIntegrand I i) (Y, r)) :
    ContDiffAt ℝ 1 (fun Z => exitClockLogMultiplier I i Z s) Y ∧
      fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y =
        ∫ r in (0 : ℝ)..s, (fderiv ℝ (exitClockRateIntegrand I i) (Y, r)).comp
          (ContinuousLinearMap.inl ℝ ExitTailState ℝ) := by
  exact ⟨contDiffAt_intervalIntegral_of_contDiffAt hs H,
    (hasFDerivAt_intervalIntegral_of_contDiffAt hs H).fderiv⟩

theorem exitClockLogMultiplier_derivative_bound {I : Set ℝ} {Y : ExitTailState} {s K : ℝ}
    (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hΦ : ∀ r ∈ Icc 0 s, ContDiffAt ℝ 1 (exitClockFlow I) (Y, r))
    (hreg : ∀ r ∈ Icc 0 s, (7 / 4 ≤ exitClockFlow I (Y, r) 0 ∧ exitClockFlow I (Y, r) 0 ≤ 17 / 4) ∧
      |exitClockFlow I (Y, r) 1| ≤ 1 / 100 ∧ |exitClockFlow I (Y, r) 2| ≤ 1 / 100)
    (hbound : ∀ r ∈ Icc 0 s, ‖fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y‖ ≤ K) (i : Fin 2) :
    ContDiffAt ℝ 1 (fun Z => exitClockLogMultiplier I i Z s) Y ∧
      ‖fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y‖ ≤ 1536 * K * s := by
  have hv (r : ℝ) (hr : r ∈ Icc 0 s) : 0 ≤ Real.exp (-r) ∧ Real.exp (-r) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.1)⟩
  have hsep (r : ℝ) (hr : r ∈ Icc 0 s) :
      (Real.exp (-r)) ^ 2 < (exitClockFlow I (Y, r) 0) ^ 2 := by
    have HR := (hreg r hr).1.1
    nlinarith only [HR, (hv r hr).1, (hv r hr).2]
  have hd (r : ℝ) (hr : r ∈ Icc 0 s) :
      exitTailSpeed (exitClockFlow I (Y, r) 0) (exitClockFlow I (Y, r) 1)
        (Real.exp (-r)) (exitClockFlow I (Y, r) 2) ≠ 0 := by
    have H := exitTailSpeed_compact (hreg r hr).1.1 (hreg r hr).2.1 (hv r hr) (hreg r hr).2.2
    linarith only [H]
  obtain ⟨HC, HD⟩ := exitClockLogMultiplier_regular hs i
    (fun r hr => contDiffAt_exitClockRateIntegrand (hΦ r hr) (hsep r hr) (hd r hr) i)
  refine ⟨HC, ?_⟩
  rw [HD]
  have HI := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := s) (C := 1536 * K)
    (f := fun r => (fderiv ℝ (exitClockRateIntegrand I i) (Y, r)).comp
      (ContinuousLinearMap.inl ℝ ExitTailState ℝ)) ?_
  · simpa only [sub_zero, abs_of_nonneg hs] using HI
  · intro r hr
    have hr' : r ∈ Icc 0 s := uIcc_of_le hs ▸ uIoc_subset_uIcc hr
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change |fderiv ℝ (exitClockRateIntegrand I i) (Y, r) (v, 0)| ≤ _
    rw [exitClockRateIntegrand_partial (hΦ r hr') (hsep r hr') (hd r hr') i v]
    have H := exitTailWallRate_direction_norm_bound (hreg r hr').1 (hreg r hr').2.1
      (hv r hr') (hreg r hr').2.2 (fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y v) i
    have HV := ((fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hbound r hr') (norm_nonneg v))
    exact H.trans (by nlinarith only [HV])

end BianchiIX
