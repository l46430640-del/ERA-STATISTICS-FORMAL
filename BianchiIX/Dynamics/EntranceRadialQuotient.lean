import BianchiIX.Dynamics.EntranceRadialPullback
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem EntranceRadialInverseAt.radius_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ) (v : ProjectiveState) :
    fderiv ℝ (fun z => entranceStableRadius (Ψ z)) (entranceRadialCoordinates y) v = v 0 := by
  have heq : (fun z => entranceStableRadius (Ψ z)) =ᶠ[𝓝 (entranceRadialCoordinates y)] (fun z => z 0) := by
    filter_upwards [H.right_inverse] with z hz
    simpa [entranceRadialCoordinates] using congrArg (fun x : ProjectiveState => x 0) hz
  rw [heq.fderiv_eq, (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) (entranceRadialCoordinates y)).fderiv]
  rfl

theorem EntranceRadialInverseAt.radial_quotient_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    {f : ProjectiveState → ℝ} (hf : DifferentiableAt ℝ f y)
    (hr0 : entranceStableRadius y ≠ 0) (hD0 : entranceClockRate y ≠ 0) (v : ProjectiveState) :
    fderiv ℝ (fun z => f (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z)))
        (entranceRadialCoordinates y) v =
      fderiv ℝ (fun z => f (Ψ z)) (entranceRadialCoordinates y) v /
        (entranceStableRadius y * entranceClockRate y) - f y / (entranceStableRadius y * entranceClockRate y) *
        (v 0 / entranceStableRadius y +
          fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) v / entranceClockRate y) := by
  have hn : DifferentiableAt ℝ f (Ψ (entranceRadialCoordinates y)) := by rw [H.apply_base]; exact hf
  have hd : DifferentiableAt ℝ entranceClockRate (Ψ (entranceRadialCoordinates y)) := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  have hnΨ := hn.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hdΨ := hd.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hden : (entranceRadialCoordinates y) 0 * entranceClockRate (Ψ (entranceRadialCoordinates y)) ≠ 0 := by
    rw [H.apply_base]
    exact mul_ne_zero hr0 hD0
  have heq : (fun z => f (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z))) =ᶠ[𝓝 (entranceRadialCoordinates y)]
      (fun z => f (Ψ z) / (z 0 * entranceClockRate (Ψ z))) := by
    filter_upwards [H.right_inverse] with z hz
    have hr : entranceStableRadius (Ψ z) = z 0 := by
      simpa [entranceRadialCoordinates] using congrArg (fun x : ProjectiveState => x 0) hz
    rw [hr]
  have hq := hnΨ.hasFDerivAt.mul ((hasFDerivAt_inv hden).comp (entranceRadialCoordinates y)
    ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) (entranceRadialCoordinates y)).mul hdΨ.hasFDerivAt))
  change HasFDerivAt (fun z => f (Ψ z) / (z 0 * entranceClockRate (Ψ z))) _ (entranceRadialCoordinates y) at hq
  rw [heq.fderiv_eq, hq.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, Function.comp_def, Pi.mul_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [H.apply_base]
  simp only [entranceRadialCoordinates, Matrix.cons_val_zero]
  field_simp
  ring

theorem EntranceRadialInverseAt.clock_quotient_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    {f : ProjectiveState → ℝ} (hf : DifferentiableAt ℝ f y)
    (hD0 : entranceClockRate y ≠ 0) (v : ProjectiveState) :
    fderiv ℝ (fun z => f (Ψ z) / entranceClockRate (Ψ z)) (entranceRadialCoordinates y) v =
      fderiv ℝ (fun z => f (Ψ z)) (entranceRadialCoordinates y) v / entranceClockRate y -
        f y * fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) v / entranceClockRate y ^ 2 := by
  have hn : DifferentiableAt ℝ f (Ψ (entranceRadialCoordinates y)) := by rw [H.apply_base]; exact hf
  have hd : DifferentiableAt ℝ entranceClockRate (Ψ (entranceRadialCoordinates y)) := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  have hnΨ := hn.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hdΨ := hd.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hden : entranceClockRate (Ψ (entranceRadialCoordinates y)) ≠ 0 := by rw [H.apply_base]; exact hD0
  have hq := hnΨ.hasFDerivAt.mul ((hasFDerivAt_inv hden).comp (entranceRadialCoordinates y) hdΨ.hasFDerivAt)
  change HasFDerivAt (fun z => f (Ψ z) / entranceClockRate (Ψ z)) _ (entranceRadialCoordinates y) at hq
  rw [hq.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply, H.apply_base]
  field_simp
  ring

end BianchiIX
