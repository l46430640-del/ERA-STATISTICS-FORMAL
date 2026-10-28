import BianchiIX.Dynamics.PartialCoreRadialMultipliers
import BianchiIX.Dynamics.PartialCoreRadialCurve
import BianchiIX.Dynamics.PartialCoreContraction
import BianchiIX.Algebra.PartialCoreRadialCone

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem partialCore_firstReturn_contraction {k Z T : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hz : projectiveCoreAngle y ≤ Z)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T) :
    projectiveOriginalFlow y 0 T 1 ≤ y 1 * Real.exp (-k / 12) ∧
      projectiveOriginalFlow y 0 T 3 ≤ y 2 * y 3 := by
  obtain ⟨S, _, hfirstS, hreg, _⟩ := exists_partialCore_entry_variation hk hy hR hV
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hreg
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hzero := projectiveOriginalFlow_initial hD (0 : ℝ)
  have hz0 : coreAngle (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) ≤ Z := by
    rw [hzero]
    exact hz
  have H := normalized_partialCore_exit_contraction hc hk le_rfl hfirst.1.1 hZ hkZ
    (fun t ht => (hreg t ht).1) (fun t ht => (hreg t ht).2) hz0 hfirst.1.2
  have HC := H.2.2
  change projectiveOriginalFlow y 0 T 1 ≤ projectiveOriginalFlow y 0 0 1 * Real.exp (-k / 12) ∧
    projectiveOriginalFlow y 0 T 3 ≤ projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3 at HC
  rwa [hzero] at HC

/-- The actual return has the square-root cone estimate once its entrance radial error is small. -/
theorem exists_partialCore_radial_cone {Y : ℝ → ProjectiveState} {x r K D Z : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hD : 0 < D) (hZ : 0 ≤ Z)
    (hY : DifferentiableAt ℝ Y x) :
    let k := fun a => coreRadius (Y a 0) (Y a 2)
    let U := fun a => Y a 1
    let p := fun a => Y a 2 * Y a 3
    let z := fun a => projectiveCoreAngle (Y a)
    let A := (200 * coreVariationBound + 2) * K ^ 2
    let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
    6 ≤ k x → coreRegion (k x) (Y x) → 1 < Y x 2 →
    2 * Real.cosh Z ≤ k x → z x ≤ Z →
    2 / (K * r) ≤ k x → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
    1 / (D * r ^ 2) ≤ -deriv k x →
    |deriv U x| ≤ K * U x / r → |deriv p x| ≤ K * p x / r → |deriv z x| ≤ K / r →
    4 * (4096 * coreVariationBound) * K ^ 2 * (U x + r * p x) ≤ 1 / (2 * D) →
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y x) 0 t 2 = 1} T ∧
      ∃ τ : ProjectiveState → ℝ, τ (Y x) = T ∧ ContDiffAt ℝ 2 τ (Y x) ∧
        (∀ᶠ y in 𝓝 (Y x), IsLeast {t | 0 < t ∧
          t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
        let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
          (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
        let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
        let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
        DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ fU x ∧ DifferentiableAt ℝ fP x ∧
        1 / (2 * D * r ^ 2) ≤ -deriv f x ∧
        |deriv f x| ≤ (K + 1 / (2 * D)) / r ^ 2 ∧
        0 ≤ fU x ∧ 0 ≤ fP x ∧ fU x ≤ U x * Real.exp (-k x / 12) ∧ fP x ≤ p x ∧
        |deriv fU x| ≤ (2 * D * (K + 24 * A) * Real.sqrt (U x)) * Real.sqrt (fU x) * |deriv f x| ∧
        |deriv fP x| ≤ (2 * D * K * (1 + B) * r * Real.sqrt (p x)) * Real.sqrt (fP x) * |deriv f x| ∧
        (U x = 0 → fU x = 0 ∧ deriv fU x = 0) ∧
        (p x = 0 → fP x = 0 ∧ deriv fP x = 0) := by
  intro k U p z A B hk hy hV hkZ hz hklo hkhi hdk hdklo hdU hdp hdz hsmall
  have hr0 := hr.1
  have hK0 : 0 < K := by linarith only [hK]
  have hk0 : 0 < k x := by linarith only [hk]
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    nlinarith only [H]
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hf, _, _, _, _, hde, _⟩ :=
    exists_partialCore_radial_curve_response hr hK hY hk hy hV hklo hkhi hdk hdU hdp hdz
  let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
    (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
  have hkd : DifferentiableAt ℝ k x := by
    have H := ((contDiffAt_toCoreAngleState 1 (zero_lt_one.trans hV)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
    exact (hasDerivAt_pi.mp H 0).differentiableAt
  change DifferentiableAt ℝ f x at hf
  change |deriv (fun a => f a - k a) x| ≤
    4 * (4096 * coreVariationBound) * K ^ 2 * (U x + r * p x) / r ^ 2 at hde
  rw [deriv_fun_sub hf hkd] at hde
  have he : |deriv f x - deriv k x| ≤ 1 / (2 * D * r ^ 2) := hde.trans
    ((div_le_div_of_nonneg_right hsmall (sq_nonneg r)).trans_eq (by ring))
  have hslope : 1 / (2 * D * r ^ 2) ≤ -deriv f x := by
    have H := (abs_le.mp he).2
    have heq : 1 / (D * r ^ 2) = 2 * (1 / (2 * D * r ^ 2)) := by ring
    rw [heq] at hdklo
    linarith only [H, hdklo]
  have hfhi : |deriv f x| ≤ (K + 1 / (2 * D)) / r ^ 2 := by
    calc
      _ = |deriv k x + (deriv f x - deriv k x)| := by congr 1; ring
      _ ≤ |deriv k x| + |deriv f x - deriv k x| := abs_add_le _ _
      _ ≤ K / r ^ 2 + 1 / (2 * D * r ^ 2) := add_le_add hdk he
      _ = _ := by ring
  have hfirstnear := hnear.mono fun _ h => h.1
  obtain ⟨_, _, _, _, _, hDU, hDP, hu0, hp0, hdu, hdpout, hzeroU, hzeroP⟩ :=
    partialCore_radial_multiplier_response hr hK hY hfirstnear hk hy hV hki hkhi hdk hdU hdp hdz
  have HC := partialCore_firstReturn_contraction hk hy rfl hV hZ hkZ hz hfirst
  rw [← hτ] at HC
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have Hcone := partial_core_radial_cone hr hK0.le hk hkhi hA hB (by positivity : 0 < 2 * D)
    hy.2.2.1.1 hy.2.2.2.1 hu0 hp0 HC.1 HC.2 hdu hdpout (hslope.trans (neg_le_abs _))
  exact ⟨T, hT, hfirst, τ, hτ, hcτ, hfirstnear, hf, hDU, hDP, hslope, hfhi,
    hu0, hp0, HC.1, HC.2, Hcone.1, Hcone.2, hzeroU, hzeroP⟩

end BianchiIX
