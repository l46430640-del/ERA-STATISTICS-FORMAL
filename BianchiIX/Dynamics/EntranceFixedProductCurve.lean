import BianchiIX.Dynamics.EntranceFixedProduct

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Radial entrance coordinates with constant strong wall and active-weak wall product. -/
def entranceFixedProductCurve (z : ProjectiveState) (t : ℝ) : ProjectiveState :=
  ![z 0, z 1, z 2 * Real.exp t, z 3 * Real.exp (-t)]

theorem entranceFixedProductCurve_zero (z : ProjectiveState) : entranceFixedProductCurve z 0 = z := by
  ext i
  fin_cases i <;> simp [entranceFixedProductCurve]

theorem entranceFixedProductCurve_invariants (z : ProjectiveState) (t : ℝ) :
    entranceFixedProductCurve z t 0 = z 0 ∧ entranceFixedProductCurve z t 1 = z 1 ∧
      entranceFixedProductCurve z t 2 * entranceFixedProductCurve z t 3 = z 2 * z 3 := by
  refine ⟨rfl, rfl, ?_⟩
  change (z 2 * Real.exp t) * (z 3 * Real.exp (-t)) = z 2 * z 3
  calc
    _ = (z 2 * z 3) * Real.exp (t + -t) := by rw [Real.exp_add]; ring
    _ = _ := by simp

theorem hasDerivAt_entranceFixedProductCurve (z : ProjectiveState) :
    HasDerivAt (entranceFixedProductCurve z)
      ((z 2) • Pi.single 2 1 - (z 3) • Pi.single 3 1) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [entranceFixedProductCurve] using hasDerivAt_const (0 : ℝ) (z 0)
  · simpa [entranceFixedProductCurve] using hasDerivAt_const (0 : ℝ) (z 1)
  · simpa [entranceFixedProductCurve] using (Real.hasDerivAt_exp 0).const_mul (z 2)
  · simpa [entranceFixedProductCurve] using ((hasDerivAt_id (0 : ℝ)).neg.exp).const_mul (z 3)

theorem hasDerivAt_entranceFixedProductCurve_comp {f : ProjectiveState → ℝ} {z : ProjectiveState}
    (hf : DifferentiableAt ℝ f z) :
    HasDerivAt (fun t => f (entranceFixedProductCurve z t))
      (z 2 * fderiv ℝ f z (Pi.single 2 1) - z 3 * fderiv ℝ f z (Pi.single 3 1)) 0 := by
  have hf' : HasFDerivAt f (fderiv ℝ f z) (entranceFixedProductCurve z 0) := by
    simpa only [entranceFixedProductCurve_zero] using hf.hasFDerivAt
  have H := hf'.comp_hasDerivAt 0 (hasDerivAt_entranceFixedProductCurve z)
  simpa only [Function.comp_def, map_sub, map_smul, smul_eq_mul] using H

theorem EntranceRadialInverseAt.fixed_product_curve_invariants {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ) :
    let z := entranceRadialCoordinates y
    ∀ᶠ t in 𝓝 (0 : ℝ),
      entranceStableRadius (Ψ (entranceFixedProductCurve z t)) = entranceStableRadius y ∧
      Ψ (entranceFixedProductCurve z t) 1 = y 1 ∧
      Ψ (entranceFixedProductCurve z t) 2 * Ψ (entranceFixedProductCurve z t) 3 = y 2 * y 3 := by
  intro z
  have ht : Tendsto (entranceFixedProductCurve z) (𝓝 0) (𝓝 z) := by
    simpa only [entranceFixedProductCurve_zero] using (hasDerivAt_entranceFixedProductCurve z).continuousAt.tendsto
  filter_upwards [ht.eventually HΨ.right_inverse] with t h
  have hi (i : Fin 4) := congrArg (fun p : ProjectiveState => p i) h
  refine ⟨?_, ?_, ?_⟩
  · simpa [entranceRadialCoordinates, entranceFixedProductCurve, z] using hi 0
  · simpa [entranceRadialCoordinates, entranceFixedProductCurve, z] using hi 1
  · have hp : Ψ (entranceFixedProductCurve z t) 2 * Ψ (entranceFixedProductCurve z t) 3 =
        entranceFixedProductCurve z t 2 * entranceFixedProductCurve z t 3 := by
      simpa [entranceRadialCoordinates] using congrArg (fun p : ProjectiveState => p 2 * p 3) h
    exact hp.trans (entranceFixedProductCurve_invariants z t).2.2

/-- The bound is the derivative along an actual curve preserving r, u and vw. -/
theorem exists_entrance_fixed_product_response :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      let g := fun t => F (entranceFixedProductCurve z t)
      ContDiffAt ℝ 2 F z ∧
      HasDerivAt g (y 2 * fderiv ℝ F z (Pi.single 2 1) - y 3 * fderiv ℝ F z (Pi.single 3 1)) 0 ∧
      |deriv g 0| ≤ C * (y 1 * y 2 + (y 2 * y 3) ^ 2 / k ^ 2) := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_fixed_product_bound
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y k hk hm hu hv hw
  obtain ⟨Ψ, HΨ, hF, _, H⟩ := HC y hk hm hu hv hw
  refine ⟨Ψ, HΨ, ?_⟩
  intro z F g
  have HD : HasDerivAt g
      (y 2 * fderiv ℝ F z (Pi.single 2 1) - y 3 * fderiv ℝ F z (Pi.single 3 1)) 0 :=
    hasDerivAt_entranceFixedProductCurve_comp (hF.differentiableAt (by norm_num))
  exact ⟨hF, HD, by rw [HD.deriv]; exact H⟩

end BianchiIX
