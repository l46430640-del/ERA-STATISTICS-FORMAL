import BianchiIX.Dynamics.PartialCoreDownwardMultipliers
import BianchiIX.Algebra.PartialCoreRadialMultiplierBounds
import BianchiIX.Analysis.MultiplierRadialDerivative

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Radial logarithmic bounds and zero-wall responses use the same fixed downward return. -/
theorem partialCoreDownwardReturn_radial_multipliers {Y : ℝ → ProjectiveState} {x r K : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hY : DifferentiableAt ℝ Y x) :
    let τ := partialCoreDownwardReturnTime
    let k := fun a => coreRadius (Y a 0) (Y a 2)
    let U := fun a => Y a 1
    let p := fun a => Y a 2 * Y a 3
    let z := fun a => projectiveCoreAngle (Y a)
    let m := fun i a => partialCoreReturnMultiplier τ (Y a) i
    let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
    let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
    let A := (200 * coreVariationBound + 2) * K ^ 2
    let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
    let L := Real.log (4 * k x)
    6 ≤ k x → coreRegion (k x) (Y x) → (1 < Y x 2 ∨ (Y x 2 = 1 ∧ 1 ≤ Y x 0)) →
    1 / k x ≤ K * r → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
    |deriv U x| ≤ K * U x / r → |deriv p x| ≤ K * p x / r → |deriv z x| ≤ K / r →
    (∀ i : Fin 2, 0 < m i x ∧ DifferentiableAt ℝ (m i) x ∧
      DifferentiableAt ℝ (fun a => Real.log (m i a)) x) ∧
    (fU =ᶠ[𝓝 x] fun a => U a * m 0 a) ∧ (fP =ᶠ[𝓝 x] fun a => p a * m 1 a) ∧
    |deriv (fun a => Real.log (m 0 a)) x| ≤ A * L / r ^ 2 ∧
    |deriv (fun a => Real.log (m 1 a)) x| ≤ B * L ∧
    DifferentiableAt ℝ fU x ∧ DifferentiableAt ℝ fP x ∧ 0 ≤ fU x ∧ 0 ≤ fP x ∧
    |deriv fU x| ≤ fU x * (K / r + A * L / r ^ 2) ∧
    |deriv fP x| ≤ fP x * (K / r + B * L) ∧
    (U x = 0 → fU x = 0 ∧ deriv fU x = 0) ∧
    (p x = 0 → fP x = 0 ∧ deriv fP x = 0) := by
  intro τ k U p z m fU fP A B L hk hy hV hki hkhi hdk hdU hdp hdz
  have hk0 : 0 < k x := by linarith only [hk]
  have hv : 0 < Y x 2 := zero_lt_one.trans_le hy.2.1
  obtain ⟨hnear, hreg, Hbound⟩ := partialCoreDownwardReturn_multiplier_response hk hy rfl hV
  have hmreg (i : Fin 2) : 0 < m i x ∧ DifferentiableAt ℝ (m i) x ∧
      DifferentiableAt ℝ (fun a => Real.log (m i a)) x :=
    ⟨(hreg i).1, ((hreg i).2.2.differentiableAt (by norm_num)).comp x hY,
      ((hreg i).2.1.differentiableAt (by norm_num)).comp x hY⟩
  have hformula : ∀ᶠ a in 𝓝 x, fU a = U a * m 0 a ∧ fP a = p a * m 1 a :=
    hY.continuousAt.tendsto.eventually hnear
  have hin := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hz := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hdk' : HasDerivAt k (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 0) x := hasDerivAt_pi.mp hin 0
  have hdU' : HasDerivAt U (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 1) x := hasDerivAt_pi.mp hin 1
  have hdp' : HasDerivAt p (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 2) x := hasDerivAt_pi.mp hin 2
  change HasDerivAt z (fderiv ℝ projectiveCoreAngle (Y x) (deriv Y x)) x at hz
  have hdl (i : Fin 2) : HasDerivAt (fun a => Real.log (m i a))
      (fderiv ℝ (fun y => Real.log (partialCoreReturnMultiplier τ y i)) (Y x) (deriv Y x)) x :=
    ((hreg i).2.1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have H := Hbound (deriv Y x)
  dsimp only [partialCoreVariationBudget] at H
  rw [← hdk'.deriv, ← hdU'.deriv, ← hdp'.deriv, ← hz.deriv, ← (hdl 0).deriv, ← (hdl 1).deriv] at H
  have hp : 0 ≤ p x ∧ p x ≤ 1 :=
    ⟨hy.2.2.2.1, (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)⟩
  have hku : k x * U x ≤ 1 := by
    have Hku := (le_div_iff₀ hk0).mp hy.2.2.1.2
    change U x * k x ≤ 1 / 10000 at Hku
    nlinarith only [Hku]
  have HQ := partial_core_radial_variation_budget hr hK hk0 hki hkhi hy.2.2.1.1 hku hp hdk hdU hdp hdz
  have Hlog := partial_core_radial_log_bounds hr.1 hK hk0 (Real.exp_pos _).le
    (core_log_lower_bound hk) hki hkhi HQ hdz H.1 H.2
  have HU := multiplier_radial_derivative (a := K / r) hdU'.differentiableAt (hmreg 0).2.1 hy.2.2.1.1 (hmreg 0).1
    (hformula.mono fun _ ha => ha.1) (hdU.trans_eq (by ring)) Hlog.1
  have HP := multiplier_radial_derivative (a := K / r) hdp'.differentiableAt (hmreg 1).2.1 hp.1 (hmreg 1).1
    (hformula.mono fun _ ha => ha.2) (hdp.trans_eq (by ring)) Hlog.2
  exact ⟨hmreg, hformula.mono fun _ ha => ha.1, hformula.mono fun _ ha => ha.2,
    Hlog.1, Hlog.2, HU.1, HP.1, HU.2.1, HP.2.1, HU.2.2.2.1, HP.2.2.2.1,
    HU.2.2.2.2, HP.2.2.2.2⟩

end BianchiIX
