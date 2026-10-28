import BianchiIX.Dynamics.PartialCoreBoundaryMultipliers
import BianchiIX.Dynamics.PartialCoreZeroVariation
import BianchiIX.Dynamics.PartialCoreMultiplierResponse

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The reference calculation applies to any regular return with its actual multiplier and variation identities. -/
theorem partialCore_boundary_response_of_return {k z : ℝ} (hk : 6 ≤ k)
    (τ : ProjectiveState → ℝ)
    (hcτ : ContDiffAt ℝ 2 τ (referencePulse k (z / k)))
    (hpos : 0 < τ (referencePulse k (z / k)))
    (htime : τ (referencePulse k (z / k)) = referenceShiftClock k (z / k) (referenceHalfTime k))
    (hnear : ∀ᶠ x in 𝓝 (referencePulse k (z / k)),
      projectiveOriginalFlow x 0 (τ x) 2 = 1 ∧
      projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
      projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1)
    (hMu : ∀ i : Fin 2, 0 < partialCoreReturnMultiplier τ (referencePulse k (z / k)) i ∧
      ContDiffAt ℝ 1 (fun x => Real.log (partialCoreReturnMultiplier τ x i)) (referencePulse k (z / k)) ∧
      ContDiffAt ℝ 1 (fun x => partialCoreReturnMultiplier τ x i) (referencePulse k (z / k)))
    (hreg : ∀ t ∈ Icc 0 (τ (referencePulse k (z / k))),
      0 < 1 + normalizedMaxCurve (fromProjectiveState (referencePulse k (z / k))) 0 t 0 ∧
      coreRegion k (projectiveOriginalFlow (referencePulse k (z / k)) 0 t))
    (hnorm : ∀ t ∈ Icc 0 (τ (referencePulse k (z / k))), ∀ w : ProjectiveState,
      ‖scaleCoreVariation k (coreProjectedFlowVariation (referencePulse k (z / k)) 0 t w)‖ ≤
        4 * coreVariationBound * partialCoreVariationBudget k
          (referencePulse k (z / k) 1) (referencePulse k (z / k) 2 * referencePulse k (z / k) 3)
          (fderiv ℝ toCoreAngleState (referencePulse k (z / k)) w)
          (fderiv ℝ projectiveCoreAngle (referencePulse k (z / k)) w)) :
    let y := referencePulse k (z / k)
    partialCoreReturnMultiplier τ y 0 =
        (k / Real.cosh z) * Real.exp (-(k / 2) * (Real.arcosh k - z)) ∧
      partialCoreReturnMultiplier τ y 1 = Real.exp (-2 * (Real.arcosh k - z) / k) ∧
      HasDerivAt (fun u : ℝ =>
        let x := fromCoreAngleState z ![k, u, 0]
        let b := projectiveOriginalFlow x 0 (τ x)
        coreRadius (b 0) (b 2) - k)
        (-2 / Real.cosh z * (1 - Real.exp (-(k / 2) * (Real.arcosh k - z)))) 0 ∧
      HasDerivAt (fun a => Real.log (partialCoreReturnMultiplier τ (referencePulse k (a / k)) 0))
        (k / 2 - Real.tanh z) z ∧
      HasDerivAt (fun a => Real.log (partialCoreReturnMultiplier τ (referencePulse k (a / k)) 1))
        (2 / k) z := by
  intro y
  have hk0 : 0 < k := by linarith only [hk]
  have hk1 : 1 < k := by linarith only [hk]
  have hD : 0 < projectiveStateDenom y := referencePulse_denom_pos k _
  have hc := fromProjectiveState_constraint hD.ne'
  have hexp : -(k ^ 2 / 2) * (referenceHalfTime k - z / k) =
      -(k / 2) * (Real.arcosh k - z) := by
    dsimp [referenceHalfTime]
    field_simp
  have hweakexp : -2 * (referenceHalfTime k - z / k) = -2 * (Real.arcosh k - z) / k := by
    dsimp [referenceHalfTime]
    ring
  have hvalues := partialCoreReturn_reference_multipliers hk1 (z / k)
    (hcτ.differentiableAt (by norm_num)) htime
    (fun i => (hMu i).2.2.differentiableAt (by norm_num)) (hnear.mono fun _ h => h.2)
  rw [mul_div_cancel₀ _ hk0.ne', hexp, hweakexp] at hvalues
  have hout : projectiveOriginalFlow y 0 (τ y) = referencePulse k (referenceHalfTime k) := by
    rw [htime]
    exact referenceShiftClock_projective_orbit _ _ _
  have hdom : Icc 0 (τ y) ⊆ normalizedMaxDomain (fromProjectiveState y) 0 :=
    fun _ ht => normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1
  have hA := fun t ht => (hreg t ht).1
  have hcore := fun t ht => (hreg t ht).2
  have hcτ₁ : ContDiffAt ℝ 1 τ y := hcτ.of_le (by norm_num)
  have hM : projectiveOriginalFlow y 0 (τ y) 0 < 1 := by
    rw [hout, referencePulse_exit hk1]
    change 1 - Real.sqrt (k ^ 2 - 1) < 1
    linarith only [referenceCoreGap_pos hk1]
  have hhit : ∀ᶠ x in 𝓝 y, projectiveOriginalFlow x 0 (τ x) 2 = 1 :=
    hnear.mono fun _ h => h.1
  let γ := fun a => referencePulse k (a / k)
  let w := (1 / k) • projectiveField y
  have hγ : HasDerivAt γ w z := (referencePulse_angle_variation hk0 z).1
  have hY : fderiv ℝ toCoreAngleState y w = 0 := (referencePulse_angle_variation hk0 z).2.1
  have hθ : fderiv ℝ projectiveCoreAngle y w = 1 := (referencePulse_angle_variation hk0 z).2.2
  have hbudget : partialCoreVariationBudget k (y 1) (y 2 * y 3)
      (fderiv ℝ toCoreAngleState y w) (fderiv ℝ projectiveCoreAngle y w) = 0 := by
    rw [hY]
    simp [partialCoreVariationBudget, y, referencePulse]
  have hzero (t : ℝ) (ht : t ∈ Icc 0 (τ y)) : coreProjectedFlowVariation y 0 t w = 0 := by
    have H := hnorm t ht w
    rw [hbudget, mul_zero] at H
    have He := norm_eq_zero.mp (le_antisymm H (norm_nonneg _))
    ext i
    have Hi := congrFun He i
    fin_cases i <;> simpa [scaleCoreVariation, hk0.ne'] using Hi
  have hlog (i : Fin 2) : HasDerivAt
      (fun a => Real.log (partialCoreReturnMultiplier τ (γ a) i))
      (-coreLogRates z ![k, 0, 0] i) z := by
    have HD := ((hMu i).2.1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt z hγ
    have HE := partialCoreReturn_log_derivative_of_zero_variation hk hD hcτ₁ hpos.le
      hdom hA hcore hhit hM w hzero i
    rw [hθ, mul_one, (referencePulse_core_coordinates hk0 (z / k)).1,
      (referencePulse_core_coordinates hk0 (z / k)).2, mul_div_cancel₀ _ hk0.ne'] at HE
    exact HE ▸ HD
  refine ⟨hvalues.1, hvalues.2, ?_, ?_, ?_⟩
  · let R := fun x : ProjectiveState => coreRadius (x 0) (x 2)
    let F := fun x => R (projectiveOriginalFlow x 0 (τ x))
    have hend : τ y ∈ Icc 0 (τ y) := ⟨hpos.le, le_rfl⟩
    have hflow := (contDiffAt_projectiveOriginalFlow_two hD (hdom hend) (hA _ hend)).comp y
      (contDiffAt_id.prodMk hcτ)
    have hRv : 0 < projectiveOriginalFlow y 0 (τ y) 2 := by
      rw [hout]
      exact referencePulse_active_pos hk0 _
    have hF : DifferentiableAt ℝ F y :=
      (hasFDerivAt_coreRadius_state hRv).differentiableAt.comp y
        (g := R) (f := fun x => projectiveOriginalFlow x 0 (τ x))
        (hflow.differentiableAt (by norm_num))
    have HE := referenceMovingEndpoint_radius_derivative hk0 (z / k) (referenceHalfTime k)
      (hcτ.differentiableAt (by norm_num)) htime (Pi.single 1 1)
    have hrad : fderiv ℝ R y (Pi.single 1 1) = 0 := by
      rw [referencePulse_radius_fderiv hk0]
      simp
    have HF : fderiv ℝ F y (Pi.single 1 1) =
        -2 / Real.cosh z * (1 - Real.exp (-(k / 2) * (Real.arcosh k - z))) := by
      change fderiv ℝ F y (Pi.single 1 1) = _ at HE
      rw [hrad, zero_add, Pi.single_eq_same, hexp] at HE
      rw [HE]
      dsimp only [referencePulse, Matrix.cons_val]
      rw [mul_div_cancel₀ _ hk0.ne']
      field_simp
      ring
    have he0 : fromCoreAngleState z ![k, 0, 0] = y := by
      simp [y, referencePulse, fromCoreAngleState, mul_div_cancel₀ _ hk0.ne']
    have hF' : DifferentiableAt ℝ F (fromCoreAngleState z ![k, 0, 0]) := he0.symm ▸ hF
    have HD := hF'.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_fromCoreAngleState_strong k z)
    rw [he0, HF] at HD
    exact HD.sub_const k
  · convert! hlog 0 using 1
    rw [coreLogRates_zero_walls]
    simp only [Matrix.cons_val_zero]
    ring
  · convert! hlog 1 using 1
    rw [coreLogRates_zero_walls]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    ring

/-- All three identities in (E.24) are ordinary derivatives of the same genuine first return. -/
theorem exists_partialCore_boundary_response {k z : ℝ} (hk : 6 ≤ k)
    (hz : |z| < Real.arcosh k) :
    let y := referencePulse k (z / k)
    ∃ τ : ProjectiveState → ℝ, 0 < τ y ∧ ContDiffAt ℝ 2 τ y ∧
      (∀ᶠ x in 𝓝 y,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState x) 0 ∧
          projectiveOriginalFlow x 0 t 2 = 1} (τ x) ∧
        projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
        projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1) ∧
      partialCoreReturnMultiplier τ y 0 =
        (k / Real.cosh z) * Real.exp (-(k / 2) * (Real.arcosh k - z)) ∧
      partialCoreReturnMultiplier τ y 1 = Real.exp (-2 * (Real.arcosh k - z) / k) ∧
      HasDerivAt (fun u : ℝ =>
        let x := fromCoreAngleState z ![k, u, 0]
        let b := projectiveOriginalFlow x 0 (τ x)
        coreRadius (b 0) (b 2) - k)
        (-2 / Real.cosh z * (1 - Real.exp (-(k / 2) * (Real.arcosh k - z)))) 0 ∧
      HasDerivAt (fun a => Real.log (partialCoreReturnMultiplier τ (referencePulse k (a / k)) 0))
        (k / 2 - Real.tanh z) z ∧
      HasDerivAt (fun a => Real.log (partialCoreReturnMultiplier τ (referencePulse k (a / k)) 1))
        (2 / k) z := by
  intro y
  have hk0 : 0 < k := by linarith only [hk]
  have hk1 : 1 < k := by linarith only [hk]
  have hs : z / k ∈ Ioo (-referenceHalfTime k) (referenceHalfTime k) := by
    constructor
    · simpa only [referenceHalfTime, neg_div] using div_lt_div_of_pos_right (abs_lt.mp hz).1 hk0
    · exact div_lt_div_of_pos_right (abs_lt.mp hz).2 hk0
  have hy : coreRegion k y := referencePulse_core_region hk hs
  have hR : coreRadius (y 0) (y 2) = k := referencePulse_radius hk0.le _
  have hV : 1 < y 2 := referencePulse_above_section hk1 hs
  have hD : 0 < projectiveStateDenom y := referencePulse_denom_pos k _
  have hc := fromProjectiveState_constraint hD.ne'
  obtain ⟨τ, hpos, hcτ, hnear, hMu, _⟩ := exists_partialCore_multiplier_response hk hy hR hV
  have hfirst := hnear.self_of_nhds.1
  have href := referencePulse_interior_firstReturn hk1 hs
  have htime : τ y = referenceShiftClock k (z / k) (referenceHalfTime k) := hfirst.unique href.2.1
  obtain ⟨S, hSpos, hfirstS, hreg, hnorm⟩ := exists_partialCore_entry_variation hk hy hR hV
  have hfirstS' : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1} S :=
    ⟨⟨hSpos, normalizedMaxDomain_contains_Ici_of_constraint hc 0 hSpos.le, hfirstS.1.2⟩,
      fun _ ht => hfirstS.2 ⟨ht.1, ht.2.2⟩⟩
  have hS : S = τ y := hfirstS'.unique hfirst
  rw [hS] at hreg hnorm
  refine ⟨τ, hpos, hcτ, hnear, ?_⟩
  exact partialCore_boundary_response_of_return hk τ hcτ hpos htime
    (hnear.mono fun _ h => ⟨h.1.1.2.2, h.2⟩) hMu hreg hnorm

end BianchiIX
