import BianchiIX.Dynamics.PartialCoreDownwardBounds
import BianchiIX.Algebra.PartialCoreRadialResponseBounds
import BianchiIX.Analysis.PartialCoreReciprocalError

noncomputable section

namespace BianchiIX

open Set

/-- The canonical downward return satisfies (E.25) on radial curves through the incoming boundary. -/
theorem partialCoreDownwardReturn_radial_response {Y : ℝ → ProjectiveState} {x r K : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hY : DifferentiableAt ℝ Y x) :
    let k := fun a => coreRadius (Y a 0) (Y a 2)
    let U := fun a => Y a 1
    let p := fun a => Y a 2 * Y a 3
    let z := fun a => projectiveCoreAngle (Y a)
    let C := 4096 * coreVariationBound
    let f := fun a => partialCoreDownwardReturnState (Y a) 0
    6 ≤ k x → coreRegion (k x) (Y x) → (1 < Y x 2 ∨ (Y x 2 = 1 ∧ 1 ≤ Y x 0)) →
    2 / (K * r) ≤ k x → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
    |deriv U x| ≤ K * U x / r → |deriv p x| ≤ K * p x / r →
    |deriv z x| ≤ K / r →
    DifferentiableAt ℝ f x ∧ k x / 2 ≤ f x ∧ f x ≤ 2 * k x ∧
    DifferentiableAt ℝ (fun a => f a - k a) x ∧
    |f x - k x| ≤ 16 * K * (U x + r * (p x) ^ 2) ∧
    |deriv (fun a => f a - k a) x| ≤ 4 * C * K ^ 2 * (U x + r * p x) / r ^ 2 ∧
    DifferentiableAt ℝ (fun a => 2 / f a - 2 / k a) x ∧
    |2 / f x - 2 / k x| ≤ 32 * K ^ 3 * r ^ 2 * (U x + r * (p x) ^ 2) ∧
    |deriv (fun a => 2 / f a - 2 / k a) x| ≤
      (8 * C * K ^ 4 + 64 * K ^ 5) * (U x + r * p x) := by
  intro k U p z C f hk hy hV hklo hkhi hdk hdU hdp hdz
  have hk0 : 0 < k x := by linarith only [hk]
  have hK0 : 0 < K := by linarith only [hK]
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Real.exp_pos _).le
  have hv : 0 < Y x 2 := zero_lt_one.trans_le hy.2.1
  have hp : 0 ≤ p x ∧ p x ≤ 1 :=
    ⟨hy.2.2.2.1, (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)⟩
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    nlinarith only [H]
  have HR := partialCoreDownwardReturn_regular hk hy rfl hV
  have hin := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hz := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hout := (HR.2.2.1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hdki : HasDerivAt k (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 0) x := hasDerivAt_pi.mp hin 0
  have hdUi : HasDerivAt U (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 1) x := hasDerivAt_pi.mp hin 1
  have hdpi : HasDerivAt p (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 2) x := hasDerivAt_pi.mp hin 2
  have hdf : HasDerivAt f (fderiv ℝ partialCoreDownwardReturnState (Y x) (deriv Y x) 0) x :=
    hasDerivAt_pi.mp hout 0
  change HasDerivAt z (fderiv ℝ projectiveCoreAngle (Y x) (deriv Y x)) x at hz
  have Hresponse := HR.2.2.2.2 (deriv Y x)
  dsimp only at Hresponse
  rw [← hdki.deriv, ← hdUi.deriv, ← hdpi.deriv, ← hz.deriv, ← hdf.deriv] at Hresponse
  have Hbudget := partial_core_radial_derivative_budget hr hK hk0 hki hkhi hy.2.2.1.1 hp hdk hdU hdp hdz
  have Hde : |deriv f x - deriv k x| ≤ 4 * C * K ^ 2 * (U x + r * p x) / r ^ 2 :=
    Hresponse.trans ((mul_le_mul_of_nonneg_left Hbudget hC).trans_eq (by ring))
  have Hvalue := (partialCoreDownwardReturn_bounds hk hy rfl hV).2.2
    (partialCoreDownwardReturnTime (Y x)) ⟨HR.1.1.1.le, le_rfl⟩
  have Hrad := coreRegion_radius_bounds hk Hvalue.2.1
  change 99 / 100 * k x ≤ f x ∧ f x ≤ 101 / 100 * k x at Hrad
  have hflo : k x / 2 ≤ f x := by linarith only [Hrad.1, hk]
  have hfhi : f x ≤ 2 * k x := by linarith only [Hrad.2, hk]
  have Hrec := partial_core_reciprocal_radial_bounds hr hK hy.2.2.1.1 hp
    hdf.differentiableAt hdki.differentiableAt hklo hflo Hvalue.2.2.1 hdk Hde
  refine ⟨hdf.differentiableAt, hflo, hfhi, hdf.differentiableAt.sub hdki.differentiableAt,
    Hrec.2.1, ?_, Hrec.1, Hrec.2.2.1, Hrec.2.2.2⟩
  rw [deriv_fun_sub hdf.differentiableAt hdki.differentiableAt]
  exact Hde

end BianchiIX
