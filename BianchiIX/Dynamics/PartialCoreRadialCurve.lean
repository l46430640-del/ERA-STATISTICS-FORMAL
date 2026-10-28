import BianchiIX.Dynamics.PartialCoreRadiusResponse
import BianchiIX.Dynamics.PartialCoreFirstReturn
import BianchiIX.Algebra.PartialCoreRadialResponseBounds
import BianchiIX.Analysis.PartialCoreReciprocalError

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem partialCore_firstReturn_radius_bounds {k T : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T) :
    let R := coreRadius (projectiveOriginalFlow y 0 T 0) (projectiveOriginalFlow y 0 T 2)
    k / 2 ≤ R ∧ R ≤ 2 * k ∧ |R - k| ≤ 16 * (y 1 + (y 2 * y 3) ^ 2 / k) := by
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hzero := projectiveOriginalFlow_initial hD (0 : ℝ)
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) = k := by
    rw [hzero]; exact hR
  have hV0 : 1 < projectiveOriginalFlow y 0 0 2 := by rw [hzero]; exact hV
  have hU0 : 0 ≤ projectiveOriginalFlow y 0 0 1 ∧
      projectiveOriginalFlow y 0 0 1 ≤ (1 / 10000) / k := by rw [hzero]; exact hy.2.2.1
  have hP0 : 0 ≤ projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3 ∧
      projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]; exact hy.2.2.2
  obtain ⟨S, hS, hfirstS, _, _, _, _, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk le_rfl hA hR0 (Or.inl hV0) hU0 hP0
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at H
  have HT := H T ⟨hfirst.1.1.le, le_rfl⟩
  have Hrad := coreRegion_radius_bounds hk HT.2.1
  change 99 / 100 * k ≤ coreRadius (projectiveOriginalFlow y 0 T 0)
    (projectiveOriginalFlow y 0 T 2) ∧ coreRadius (projectiveOriginalFlow y 0 T 0)
    (projectiveOriginalFlow y 0 T 2) ≤ 101 / 100 * k at Hrad
  have Hval := HT.2.2.1
  change |coreRadius (projectiveOriginalFlow y 0 T 0) (projectiveOriginalFlow y 0 T 2) - k| ≤
    16 * (projectiveOriginalFlow y 0 0 1 +
      (projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3) ^ 2 / k) at Hval
  rw [hzero] at Hval
  exact ⟨by linarith only [Hrad.1, hk], by linarith only [Hrad.2, hk], Hval⟩

/-- The actual first return, pulled back along an ordinary radial curve, satisfies (E.25). -/
theorem exists_partialCore_radial_curve_response {Y : ℝ → ProjectiveState} {x r K : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hY : DifferentiableAt ℝ Y x) :
    let k := fun a => coreRadius (Y a 0) (Y a 2)
    let U := fun a => Y a 1
    let p := fun a => Y a 2 * Y a 3
    let z := fun a => projectiveCoreAngle (Y a)
    let C := 4096 * coreVariationBound
    6 ≤ k x → coreRegion (k x) (Y x) → 1 < Y x 2 →
    2 / (K * r) ≤ k x → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
    |deriv U x| ≤ K * U x / r → |deriv p x| ≤ K * p x / r →
    |deriv z x| ≤ K / r →
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y x) 0 t 2 = 1} T ∧
      ∃ τ : ProjectiveState → ℝ, τ (Y x) = T ∧ ContDiffAt ℝ 2 τ (Y x) ∧
        (∀ᶠ y in 𝓝 (Y x),
          IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
            projectiveOriginalFlow y 0 t 2 = 1} (τ y) ∧
          ∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
            0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0) ∧
        let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
          (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
        DifferentiableAt ℝ f x ∧ k x / 2 ≤ f x ∧ f x ≤ 2 * k x ∧
        DifferentiableAt ℝ (fun a => f a - k a) x ∧
        |f x - k x| ≤ 16 * K * (U x + r * (p x) ^ 2) ∧
        |deriv (fun a => f a - k a) x| ≤ 4 * C * K ^ 2 * (U x + r * p x) / r ^ 2 ∧
        DifferentiableAt ℝ (fun a => 2 / f a - 2 / k a) x ∧
        |2 / f x - 2 / k x| ≤ 32 * K ^ 3 * r ^ 2 * (U x + r * (p x) ^ 2) ∧
        |deriv (fun a => 2 / f a - 2 / k a) x| ≤
          (8 * C * K ^ 4 + 64 * K ^ 5) * (U x + r * p x) := by
  intro k U p z C hk hy hV hklo hkhi hdk hdU hdp hdz
  have hk0 : 0 < k x := by linarith only [hk]
  have hK0 : 0 < K := by linarith only [hK]
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (Real.exp_pos _).le
  have hv : 0 < Y x 2 := zero_lt_one.trans hV
  have hp : 0 ≤ p x ∧ p x ≤ 1 :=
    ⟨hy.2.2.2.1, (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)⟩
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    nlinarith only [H]
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hcF, H⟩ :=
    exists_partialCore_radius_response hk hy rfl hV
  let F := fun y => toCoreAngleState (projectiveOriginalFlow y 0 (τ y))
  let f := fun a => (F (Y a)) 0
  have hin := ((contDiffAt_toCoreAngleState 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hz := ((contDiffAt_projectiveCoreAngle 1 hv).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hout := (hcF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hdki : HasDerivAt k (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 0) x := hasDerivAt_pi.mp hin 0
  have hdUi : HasDerivAt U (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 1) x := hasDerivAt_pi.mp hin 1
  have hdpi : HasDerivAt p (fderiv ℝ toCoreAngleState (Y x) (deriv Y x) 2) x := hasDerivAt_pi.mp hin 2
  have hdf : HasDerivAt f (fderiv ℝ F (Y x) (deriv Y x) 0) x := hasDerivAt_pi.mp hout 0
  change HasDerivAt z (fderiv ℝ projectiveCoreAngle (Y x) (deriv Y x)) x at hz
  have Hresponse := H (deriv Y x)
  dsimp only at Hresponse
  rw [← hdki.deriv, ← hdUi.deriv, ← hdpi.deriv, ← hz.deriv, ← hdf.deriv] at Hresponse
  have Hbudget := partial_core_radial_derivative_budget hr hK hk0 hki hkhi hy.2.2.1.1 hp hdk hdU hdp hdz
  have Hde : |deriv f x - deriv k x| ≤ 4 * C * K ^ 2 * (U x + r * p x) / r ^ 2 :=
    Hresponse.trans ((mul_le_mul_of_nonneg_left Hbudget hC).trans_eq (by ring))
  have Hvalue := partialCore_firstReturn_radius_bounds hk hy rfl hV hfirst
  change k x / 2 ≤ coreRadius _ _ ∧ coreRadius _ _ ≤ 2 * k x ∧ _ at Hvalue
  have hfval : f x = coreRadius (projectiveOriginalFlow (Y x) 0 T 0) (projectiveOriginalFlow (Y x) 0 T 2) := by
    change coreRadius (projectiveOriginalFlow (Y x) 0 (τ (Y x)) 0) _ = _
    rw [hτ]
  rw [← hfval] at Hvalue
  have Hrec := partial_core_reciprocal_radial_bounds hr hK hy.2.2.1.1 hp
    hdf.differentiableAt hdki.differentiableAt hklo Hvalue.1 Hvalue.2.2 hdk Hde
  refine ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hdf.differentiableAt,
    Hvalue.1, Hvalue.2.1, hdf.differentiableAt.sub hdki.differentiableAt,
    Hrec.2.1, ?_, Hrec.1, Hrec.2.2.1, Hrec.2.2.2⟩
  change |deriv (fun a => f a - k a) x| ≤ _
  rw [deriv_fun_sub hdf.differentiableAt hdki.differentiableAt]
  exact Hde

end BianchiIX
