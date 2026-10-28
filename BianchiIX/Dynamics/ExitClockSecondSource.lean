import BianchiIX.Dynamics.ExitClockInterval
import BianchiIX.Analysis.ParameterSlice

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def exitClockVariationRate (I : Set ℝ) (w : ExitTailState) (p : ExitTailState × ℝ) : ExitTailState :=
  fderiv ℝ (exitTailField (Real.exp (-p.2))) (exitClockFlow I p)
    (fderiv ℝ (exitClockFlow I) p (w, 0))

theorem contDiffAt_exitClock_stateDerivative {y : ProjectiveState} (hV : 0 < y 2)
    (hm : y 0 < 1) (hd : exitClockRate y ≠ 0) :
    ContDiffAt ℝ 1 (fun p : ℝ × ExitTailState => fderiv ℝ (exitTailField (Real.exp (-p.1))) p.2)
      (exitLogClock y, toExitTailState y) := by
  have hmap : ContDiffAt ℝ 2
      (fun p : (ℝ × ExitTailState) × ExitTailState => (p.1.1, p.2))
      ((exitLogClock y, toExitTailState y), toExitTailState y) := by fun_prop
  have HF := (contDiffAt_exitClockField hV hm hd 2).comp
    ((exitLogClock y, toExitTailState y), toExitTailState y) hmap
  exact HF.fderiv (f := fun p : ℝ × ExitTailState => exitTailField (Real.exp (-p.1)))
    contDiffAt_snd (by norm_num)

theorem contDiffAt_exitClockVariationRate_one {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hΦ : ContDiffAt ℝ 2 (exitClockFlow I) (Y, s))
    (hA : ContDiffAt ℝ 1 (fun p : ℝ × ExitTailState => fderiv ℝ (exitTailField (Real.exp (-p.1))) p.2)
      (s, exitClockFlow I (Y, s))) (w : ExitTailState) :
    ContDiffAt ℝ 1 (exitClockVariationRate I w) (Y, s) := by
  have HD := hA.comp (Y, s) (contDiffAt_snd.prodMk (hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)))
  exact HD.clm_apply (contDiffAt_parameterVariation hΦ w)

/-- Differentiation at fixed clock gives exactly the Hessian forcing and the homogeneous second variation. -/
theorem exitClockVariationRate_fderiv_initial {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hΦ : ContDiffAt ℝ 2 (exitClockFlow I) (Y, s))
    (hA : ContDiffAt ℝ 1 (fun p : ℝ × ExitTailState => fderiv ℝ (exitTailField (Real.exp (-p.1))) p.2)
      (s, exitClockFlow I (Y, s))) (v w : ExitTailState) :
    fderiv ℝ (exitClockVariationRate I w) (Y, s) (v, 0) =
      fderiv ℝ (exitTailField (Real.exp (-s))) (exitClockFlow I (Y, s))
        (fderiv ℝ (fun Z => fderiv ℝ (exitClockFlow I) (Z, s) (w, 0)) Y v) +
      fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (exitClockFlow I (Y, s))
        (fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))
        (fderiv ℝ (exitClockFlow I) (Y, s) (w, 0)) := by
  have hFs := (hΦ.differentiableAt (by norm_num)).hasFDerivAt.comp Y
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y s)
  have hJs : DifferentiableAt ℝ (fun Z => fderiv ℝ (exitClockFlow I) (Z, s) (w, 0)) Y := by
    have HJ := ((contDiffAt_parameterVariation hΦ w).differentiableAt (by norm_num)).comp Y
      ((hasFDerivAt_prodMk_left (𝕜 := ℝ) Y s).differentiableAt)
    exact HJ
  have hAs : DifferentiableAt ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (exitClockFlow I (Y, s)) :=
    (hA.differentiableAt (by norm_num)).comp _
      ((hasFDerivAt_const s _).prodMk (hasFDerivAt_id _)).differentiableAt
  have Hprod := (hAs.hasFDerivAt.comp Y hFs).clm_apply hJs.hasFDerivAt
  have Hpart := ((contDiffAt_exitClockVariationRate_one hΦ hA w).differentiableAt
    (by norm_num)).hasFDerivAt.comp Y (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y s)
  have HE := congrArg (fun L : ExitTailState →L[ℝ] ExitTailState => L v) (Hpart.unique Hprod)
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, add_apply,
    ContinuousLinearMap.flip_apply] using HE

end BianchiIX
