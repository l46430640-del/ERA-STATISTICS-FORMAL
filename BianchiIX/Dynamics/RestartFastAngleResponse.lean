import BianchiIX.Dynamics.RestartFastProjectiveEntry
import BianchiIX.Analysis.ArsinhQuotientDerivative

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The core angle is differentiated before the projective denominator can introduce artificial losses. -/
theorem restartFastCoreAngle_derivative_bound {h T θ ζ ρ r M D : ℝ} {v : RestartRadialState}
    (H : HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ)
    (HA : DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ)
    (hr : 0 < r) (hM : 0 ≤ M) (hD : 0 ≤ D) (hsmall : M * r ≤ 1 / 16)
    (hp : ‖restartSectionRadialState h T (restartRadialCurve θ ζ ρ)‖ ≤ M * r)
    (hv : ‖v‖ ≤ D)
    (ha : r / 2 ≤ (restartSectionRadialState h T (restartRadialCurve θ ζ ρ)).2 1)
    (hA : 0 < restartFastProjectionHeight h T θ ζ ρ)
    (hAhi : restartFastProjectionHeight h T θ ζ ρ ≤ 10 * (M * r) ^ 2)
    (hAd : |deriv (restartFastProjectionHeight h T θ ζ) ρ| ≤ 32 * (M * r) * D) :
    DifferentiableAt ℝ (restartFastCoreAngle h T θ ζ) ρ ∧
      |deriv (restartFastCoreAngle h T θ ζ) ρ| ≤ 20 * M * D / r := by
  let P := fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)
  let A := restartFastProjectionHeight h T θ ζ
  let f := fun y => A y / Real.sqrt 3 - (P y).2 0
  let a := fun y => (P y).2 1
  change 0 < A ρ at hA
  have Hc (i : Fin 3) : HasDerivAt (fun y => (P y).2 i) (v.2 i) ρ := by
    let Q : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact Q.hasFDerivAt.comp_hasDerivAt ρ
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ H)
  have Hpc (i : Fin 3) : |(P ρ).2 i| ≤ M * r :=
    (norm_le_pi_norm (P ρ).2 i).trans ((norm_snd_le (P ρ)).trans hp)
  have Hvc (i : Fin 3) : |v.2 i| ≤ D :=
    (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have HAr : A ρ ≤ M * r := by
    have Hsmall := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hM hr.le)
    change A ρ ≤ 10 * (M * r) ^ 2 at hAhi
    nlinarith only [hAhi, Hsmall, mul_nonneg hM hr.le]
  have HAd : |deriv A ρ| ≤ 2 * D := hAd.trans (by
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hD])
  have Hf : HasDerivAt f (deriv A ρ / Real.sqrt 3 - v.2 0) ρ :=
    (HA.hasDerivAt.div_const (Real.sqrt 3)).sub (Hc 0)
  have Hfval : |f ρ| ≤ 2 * M * r := by
    have Htriangle := abs_sub_le (A ρ / Real.sqrt 3) 0 ((P ρ).2 0)
    simp only [sub_zero, zero_sub, abs_neg, abs_of_pos (div_pos hA hsqrt)] at Htriangle
    have HAs := (div_le_self hA.le hsqrt1).trans HAr
    change |A ρ / Real.sqrt 3 - (P ρ).2 0| ≤ _
    linarith only [Htriangle, HAs, Hpc 0]
  have Hfder : |deriv A ρ / Real.sqrt 3 - v.2 0| ≤ 3 * D := by
    have Htriangle := abs_sub_le (deriv A ρ / Real.sqrt 3) 0 (v.2 0)
    simp only [sub_zero, zero_sub, abs_neg, abs_div, abs_of_pos hsqrt] at Htriangle
    have HAs := (div_le_self (abs_nonneg (deriv A ρ)) hsqrt1).trans HAd
    linarith only [Htriangle, HAs, Hvc 0]
  have Hangle := arsinh_quotient_radial_derivative_bound Hf (Hc 1) hr hM hD Hfval
    ⟨ha, (le_abs_self _).trans (Hpc 1)⟩ Hfder (Hvc 1)
  have Hgerm : restartFastCoreAngle h T θ ζ =ᶠ[𝓝 ρ] (fun y => Real.arsinh (f y / a y)) := by
    filter_upwards [HA.continuousAt.eventually (isOpen_Ioi.mem_nhds hA)] with y hy
    exact coreAngle_toProjectiveState (ne_of_gt hy)
  have HD := Hangle.1.hasDerivAt.congr_of_eventuallyEq Hgerm
  exact ⟨HD.differentiableAt, by rw [HD.deriv]; exact Hangle.2⟩

end BianchiIX
