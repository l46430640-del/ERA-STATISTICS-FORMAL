import BianchiIX.Analysis.ClockVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A clock displacement contributes a total time derivative to an integral variation. -/
theorem hasDerivAt_clock_integral_boundary
    {p : E → F} {clock rate : E → ℝ} {f : E → E} {L : ℝ × F → ℝ}
    {alpha v : ℝ → E} {field : F} {t : ℝ}
    (hp : DifferentiableAt ℝ p (alpha t)) (hc : ContDiffAt ℝ 2 clock (alpha t))
    (hf : DifferentiableAt ℝ f (alpha t)) (hr : DifferentiableAt ℝ rate (alpha t))
    (hL : DifferentiableAt ℝ L (clock (alpha t), p (alpha t)))
    (ha : HasDerivAt alpha (f (alpha t)) t)
    (hv : HasDerivAt v (fderiv ℝ f (alpha t) (v t)) t)
    (hclock : (fun x => fderiv ℝ clock x (f x)) =ᶠ[𝓝 (alpha t)] rate)
    (hstate : fderiv ℝ p (alpha t) (f (alpha t)) = rate (alpha t) • field) :
    HasDerivAt (fun s => L (clock (alpha s), p (alpha s)) * fderiv ℝ clock (alpha s) (v s))
      (fderiv ℝ (fun x => rate x * L (clock x, p x)) (alpha t) (v t) -
        rate (alpha t) * fderiv ℝ (fun Y => L (clock (alpha t), Y)) (p (alpha t))
          (fderiv ℝ p (alpha t) (v t) - fderiv ℝ clock (alpha t) (v t) • field)) t := by
  let J := fderiv ℝ L (clock (alpha t), p (alpha t))
  let c := fderiv ℝ clock (alpha t) (v t)
  let w := fderiv ℝ p (alpha t) (v t)
  have hc' := (hc.differentiableAt (by norm_num)).hasFDerivAt
  have htheta : HasDerivAt (fun s => clock (alpha s)) (rate (alpha t)) t := by
    convert! hc'.comp_hasDerivAt t ha using 1
    exact hclock.self_of_nhds.symm
  have hY : HasDerivAt (fun s => p (alpha s)) (rate (alpha t) • field) t := by
    convert! hp.hasFDerivAt.comp_hasDerivAt t ha using 1
    exact hstate.symm
  have hdtheta := hasDerivAt_observable_variation hc hf ha hv
  rw [hclock.fderiv_eq] at hdtheta
  have hrate := hr.hasFDerivAt.mul (hL.hasFDerivAt.comp (alpha t) (hc'.prodMk hp.hasFDerivAt))
  change HasFDerivAt (fun x => rate x * L (clock x, p x)) _ _ at hrate
  have hslice := hL.hasFDerivAt.comp (p (alpha t))
    ((hasFDerivAt_const (clock (alpha t)) (p (alpha t))).prodMk (hasFDerivAt_id (p (alpha t))))
  change HasFDerivAt (fun Y => L (clock (alpha t), Y)) _ _ at hslice
  have hJa : J (rate (alpha t), rate (alpha t) • field) = rate (alpha t) * J (1, field) := by
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    simp
  have hJ : J (0, w - c • field) = J (c, w) - c * J (1, field) := by
    rw [← smul_eq_mul, ← map_smul, ← map_sub]
    congr 1
    ext <;> simp
  apply ((hL.hasFDerivAt.comp_hasDerivAt t (htheta.prodMk hY)).mul hdtheta).congr_deriv
  rw [hrate.fderiv, hslice.fderiv]
  change J (rate (alpha t), rate (alpha t) • field) * c +
      L (clock (alpha t), p (alpha t)) * fderiv ℝ rate (alpha t) (v t) =
    (rate (alpha t) * J (c, w) + L (clock (alpha t), p (alpha t)) *
      fderiv ℝ rate (alpha t) (v t)) - rate (alpha t) * J (0, w - c • field)
  rw [hJa, hJ]
  ring

/-- Integrating the total derivative leaves only the two clock endpoints. -/
theorem integral_eq_projected_add_boundary {g h B : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : ContinuousOn g (Icc a b)) (hh : ContinuousOn h (Icc a b))
    (hB : ∀ t ∈ Icc a b, HasDerivAt B (g t - h t) t) :
    (∫ t in a..b, g t) = (∫ t in a..b, h t) + B b - B a := by
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hB t (uIcc_of_le hab ▸ ht))
    ((hg.sub hh).intervalIntegrable_of_Icc hab)
  rw [intervalIntegral.integral_sub (hg.intervalIntegrable_of_Icc hab) (hh.intervalIntegrable_of_Icc hab)] at H
  linarith only [H]

end BianchiIX
