import BianchiIX.Dynamics.ArrivalFlux
import BianchiIX.Dynamics.MainWallChart
import Mathlib.LinearAlgebra.Alternating.Curry

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem normalizedSectionFlux_comp (x : NormalizedState)
    (L : SectionCoordinates →L[ℝ] NormalizedState) (D : SectionCoordinates →L[ℝ] SectionCoordinates) :
    normalizedSectionFlux x (fun i => L (D (Pi.single i 1))) =
      D.det * normalizedSectionFlux x (fun i => L (Pi.single i 1)) := by
  let f : SectionCoordinates [⋀^Fin 3]→ₗ[ℝ] ℝ :=
    (normalizedVolumeWeight x)⁻¹ •
      ((normalizedAmbientVolume.curryLeft ((1 / 2 : ℝ) • x)).curryLeft (normalizedField x)).compLinearMap L.toLinearMap
  let b := Pi.basisFun ℝ (Fin 3)
  have hd : b.det (D ∘ b) = D.det := by
    convert! b.det_comp D.toLinearMap b using 1
    simp only [b.det_self, mul_one]
  have H : f (D ∘ b) = D.det * f b := by
    calc
      _ = (f b • b.det) (D ∘ b) := congrArg (fun a => a (D ∘ b)) (f.eq_smul_basis_det b)
      _ = _ := by change f b * b.det (D ∘ b) = _; rw [hd, mul_comm]
  have hf (v : Fin 3 → SectionCoordinates) : f v = normalizedSectionFlux x (fun i => L (v i)) := by
    simp only [f, AlternatingMap.smul_apply, AlternatingMap.compLinearMap_apply,
      AlternatingMap.curryLeft_apply_apply, smul_eq_mul, normalizedSectionFlux,
      normalizedConstraintVolume, div_eq_mul_inv]
    rw [mul_comm]
    congr 1
  rw [hf, hf] at H
  simpa only [b, Pi.basisFun_apply, Function.comp_apply] using H

/-- Every smooth arrival between transverse constraint charts has a nonsingular coordinate derivative. -/
theorem normalized_chart_arrival_det_ne_zero
    {C D : SectionCoordinates → NormalizedState} {R : SectionCoordinates → SectionCoordinates}
    {y : SectionCoordinates} {τ : NormalizedState → ℝ} {t₀ : ℝ}
    (hC : DifferentiableAt ℝ C y) (hD : DifferentiableAt ℝ D (R y))
    (hR : DifferentiableAt ℝ R y) (hτ : DifferentiableAt ℝ τ (C y))
    (hp : positiveWalls (C y)) (hc : ∀ᶠ v in 𝓝 y, stateConstraint (C v) = 1)
    (ht : τ (C y) ∈ normalizedMaxDomain (C y) t₀)
    (hflux : normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (heq : (fun v => D (R v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (C v) t₀ (τ (C v)))) :
    (fderiv ℝ R y).det ≠ 0 := by
  let A := fun x => normalizedMaxCurve x t₀ (τ x)
  have hA := (hasFDerivAt_normalized_arrival ht hτ).differentiableAt.hasFDerivAt
  have hder : (fderiv ℝ D (R y)).comp (fderiv ℝ R y) =
      (fderiv ℝ A (C y)).comp (fderiv ℝ C y) :=
    (hD.hasFDerivAt.comp y hR.hasFDerivAt).unique ((hA.comp y hC.hasFDerivAt).congr_of_eventuallyEq heq)
  have htangent : ∀ i, normalizedConstraintDifferential (C y) (fderiv ℝ C y (Pi.single i 1)) = 0 := by
    have H := ((hasFDerivAt_stateConstraint (C y)).comp y hC.hasFDerivAt).unique
      ((hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq hc)
    intro i
    exact congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L (Pi.single i 1)) H
  have hframe : (fun i => fderiv ℝ A (C y) (fderiv ℝ C y (Pi.single i 1))) =
      (fun i => fderiv ℝ D (R y) (fderiv ℝ R y (Pi.single i 1))) := by
    funext i
    exact congrArg (fun L : SectionCoordinates →L[ℝ] NormalizedState => L (Pi.single i 1)) hder.symm
  have H := normalizedSectionFlux_arrival_abs hp hc.self_of_nhds ht hτ
    (fun i => fderiv ℝ C y (Pi.single i 1)) htangent
  have hvalue : D (R y) = normalizedMaxCurve (C y) t₀ (τ (C y)) := heq.self_of_nhds
  change |normalizedSectionFlux _ (fun i => fderiv ℝ A (C y) (fderiv ℝ C y (Pi.single i 1)))| = _ at H
  rw [← hvalue, hframe, normalizedSectionFlux_comp] at H
  intro hz
  rw [hz, zero_mul, abs_zero] at H
  exact (ne_of_gt (mul_pos (Real.exp_pos _) (abs_pos.mpr hflux))) H.symm

end BianchiIX
