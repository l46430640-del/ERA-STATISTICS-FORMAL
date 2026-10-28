import BianchiIX.Analysis.CoordinateVariation
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The variation of an observable differentiates its directional derivative along the field. -/
theorem hasDerivAt_observable_variation
    {p : E → F} {f : E → E} {alpha v : ℝ → E} {t : ℝ}
    (hp : ContDiffAt ℝ 2 p (alpha t)) (hf : DifferentiableAt ℝ f (alpha t))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t) :
    HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s))
      (fderiv ℝ (fun x => fderiv ℝ p x (f x)) (alpha t) (v t)) t := by
  have hdp : DifferentiableAt ℝ (fderiv ℝ p) (alpha t) :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hK := hdp.hasFDerivAt.clm_apply hf.hasFDerivAt
  have hsym := (hp.isSymmSndFDerivAt (by norm_num)).eq (f (alpha t)) (v t)
  have hd := (hdp.hasFDerivAt.comp_hasDerivAt t ha).clm_apply hv
  convert! hd using 1
  rw [hK.fderiv]
  change fderiv ℝ p (alpha t) (fderiv ℝ f (alpha t) (v t)) +
      fderiv ℝ (fderiv ℝ p) (alpha t) (v t) (f (alpha t)) = _
  rw [hsym, add_comm]
  rfl

/-- Removing the clock displacement leaves only the state derivative at fixed clock. -/
theorem hasDerivAt_clock_projected_variation
    {field : ℝ × E → E} {J : (ℝ × E) →L[ℝ] E}
    {theta dtheta : ℝ → ℝ} {Y dY : ℝ → E} {a b t : ℝ}
    (hfield : HasFDerivAt field J (theta t, Y t))
    (htheta : HasDerivAt theta a t)
    (hY : HasDerivAt Y (a • field (theta t, Y t)) t)
    (hdtheta : HasDerivAt dtheta b t)
    (hdY : HasDerivAt dY
      (b • field (theta t, Y t) + a • J (dtheta t, dY t)) t) :
    HasDerivAt (fun s => dY s - dtheta s • field (theta s, Y s))
      (a • J (0, dY t - dtheta t • field (theta t, Y t))) t := by
  have hF := hfield.comp_hasDerivAt t (htheta.prodMk hY)
  have hJa : J (a, a • field (theta t, Y t)) = a • J (1, field (theta t, Y t)) := by
    rw [← map_smul]
    congr 1
    simp
  have hJ : J (0, dY t - dtheta t • field (theta t, Y t)) =
      J (dtheta t, dY t) - dtheta t • J (1, field (theta t, Y t)) := by
    rw [← map_smul, ← map_sub]
    congr 1
    ext <;> simp
  apply (hdY.sub (hdtheta.smul hF)).congr_deriv
  rw [hJa, hJ]
  simp only [Function.comp_apply]
  module

/-- Coordinate variations at a fixed value of an observable clock, in the original time. -/
theorem hasDerivAt_coordinate_clock_variation
    {p : E → F} {clock rate : E → ℝ} {f : E → E} {field : ℝ × F → F}
    {alpha v : ℝ → E} {t : ℝ}
    (hp : ContDiffAt ℝ 2 p (alpha t)) (hc : ContDiffAt ℝ 2 clock (alpha t))
    (hf : DifferentiableAt ℝ f (alpha t)) (hr : DifferentiableAt ℝ rate (alpha t))
    (hfield : DifferentiableAt ℝ field (clock (alpha t), p (alpha t)))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t)
    (hclock : (fun x => fderiv ℝ clock x (f x)) =ᶠ[𝓝 (alpha t)] rate)
    (hstate : (fun x => fderiv ℝ p x (f x)) =ᶠ[𝓝 (alpha t)]
      (fun x => rate x • field (clock x, p x))) :
    HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s) -
      fderiv ℝ clock (alpha s) (v s) • field (clock (alpha s), p (alpha s)))
      (rate (alpha t) • fderiv ℝ (fun Y => field (clock (alpha t), Y)) (p (alpha t))
        (fderiv ℝ p (alpha t) (v t) -
          fderiv ℝ clock (alpha t) (v t) • field (clock (alpha t), p (alpha t)))) t := by
  have hp' := (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hc' := (hc.differentiableAt (by norm_num)).hasFDerivAt
  have htheta : HasDerivAt (fun s => clock (alpha s)) (rate (alpha t)) t := by
    convert! hc'.comp_hasDerivAt t ha using 1
    exact hclock.self_of_nhds.symm
  have hY : HasDerivAt (fun s => p (alpha s))
      (rate (alpha t) • field (clock (alpha t), p (alpha t))) t := by
    convert! hp'.comp_hasDerivAt t ha using 1
    exact hstate.self_of_nhds.symm
  have hdtheta := hasDerivAt_observable_variation hc hf ha hv
  rw [hclock.fderiv_eq] at hdtheta
  have hproduct := hr.hasFDerivAt.smul (hfield.hasFDerivAt.comp (alpha t) (hc'.prodMk hp'))
  change HasFDerivAt (fun x => rate x • field (clock x, p x)) _ _ at hproduct
  have hdY : HasDerivAt (fun s => fderiv ℝ p (alpha s) (v s))
      (fderiv ℝ rate (alpha t) (v t) • field (clock (alpha t), p (alpha t)) +
        rate (alpha t) • fderiv ℝ field (clock (alpha t), p (alpha t))
          (fderiv ℝ clock (alpha t) (v t), fderiv ℝ p (alpha t) (v t))) t := by
    apply (hasDerivAt_observable_variation hp hf ha hv).congr_deriv
    rw [hstate.fderiv_eq, hproduct.fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, Function.comp_apply]
    exact add_comm _ _
  have H := hasDerivAt_clock_projected_variation hfield.hasFDerivAt htheta hY hdtheta hdY
  have hslice := hfield.hasFDerivAt.comp (p (alpha t))
    ((hasFDerivAt_const (clock (alpha t)) (p (alpha t))).prodMk (hasFDerivAt_id (p (alpha t))))
  change HasFDerivAt (fun Y => field (clock (alpha t), Y)) _ _ at hslice
  convert! H using 1
  rw [hslice.fderiv]
  rfl

end BianchiIX
