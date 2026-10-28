import BianchiIX.Dynamics.EntranceRadialReturnDifferential
import BianchiIX.Dynamics.ConnectionLift

noncomputable section

namespace BianchiIX

open Set

theorem normalizedEventDifferential_field {g : NormalizedState → ℝ} {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) (hr : normalizedEventRate g x t₀ t ≠ 0) :
    normalizedEventDifferential g x t₀ t (normalizedField x) = 0 := by
  simp only [normalizedEventDifferential, normalizedEventTimeDifferential, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, ContinuousLinearMap.comp_apply,
    normalizedFlowDifferential_field ht]
  change normalizedField (normalizedMaxCurve x t₀ t) +
    (-(normalizedEventRate g x t₀ t)⁻¹ * normalizedEventRate g x t₀ t) •
      normalizedField (normalizedMaxCurve x t₀ t) = 0
  simp [hr]

theorem entranceReturnState_fderiv_field {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    fderiv ℝ entranceReturnState y (projectiveField y) = 0 ∧
      fderiv ℝ entranceReturnState y (entranceLogField y) = 0 := by
  have HR := entranceReturn_regular hk hm hu hv hw
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have hd := entrance_initial_denom_pos hk hm hu hv hw
  have hzero : fderiv ℝ entranceReturnState y (projectiveField y) = 0 := by
    rw [HR.2.2.2.2.1.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      fromProjectiveState_fderiv_field hd.ne', map_smul,
      normalizedEventDifferential_field (HR.1.2.1 _ ht).1 (HR.1.2.2.2 _ ht).ne', smul_zero, map_zero]
  refine ⟨hzero, ?_⟩
  rw [entranceLogField, map_smul, hzero, smul_zero]

theorem entranceRadialDifferential_logField {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    entranceRadialDifferential y (entranceLogField y) =
      ![entranceRadialDrift y, y 1 * entranceStrongLogRate y, y 2, y 3 * entranceWeakLogRate y] := by
  have hD := (entranceRegion_clock_pos hk hy).ne'
  have HE : fderiv ℝ entranceStableRadius y (entranceLogField y) = entranceRadialDrift y :=
    (entranceRadialDrift_lie_eventuallyEq hk hy hv).self_of_nhds
  obtain ⟨hU, hW⟩ := entranceWallLogRates_field hD
  rw [entranceRadialDifferential_apply, HE, entranceLogField_active hD]
  ext i
  fin_cases i
  · rfl
  · change (entranceClockRate y)⁻¹ * projectiveField y 1 = y 1 * entranceStrongLogRate y
    rw [hU]
    field_simp
  · rfl
  · change (entranceClockRate y)⁻¹ * projectiveField y 3 = y 3 * entranceWeakLogRate y
    rw [hW]
    field_simp

/-- The fourth ordinary input column follows from the exact event projection and flow transport. -/
theorem EntranceRadialInverseAt.return_observable_transport {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000)
    {p : ProjectiveState → ℝ} (hp : DifferentiableAt ℝ p (entranceReturnState y)) :
    let D := fderiv ℝ (fun z => p (entranceReturnState (Ψ z))) (entranceRadialCoordinates y)
    y 2 * D (Pi.single 2 1) + entranceRadialDrift y * D (Pi.single 0 1) +
      (y 1 * entranceStrongLogRate y) * D (Pi.single 1 1) +
      (y 3 * entranceWeakLogRate y) * D (Pi.single 3 1) = 0 := by
  intro D
  have hy : entranceRegion (coreRadius (y 0) (y 2)) y :=
    ⟨hm, by rw [sub_self, abs_zero]; linarith, hu, ⟨hv.1.le, hv.2.le⟩, hw⟩
  have hp' : HasFDerivAt p (fderiv ℝ p (entranceReturnState y))
      (entranceReturnState (Ψ (entranceRadialCoordinates y))) := by
    rw [HΨ.apply_base]
    exact hp.hasFDerivAt
  have HD := hp'.comp (entranceRadialCoordinates y) (HΨ.hasFDerivAt_return hk hm hu hv hw)
  simp only [Function.comp_def] at HD
  have Hzero : D (entranceRadialDifferential y (entranceLogField y)) = 0 := by
    dsimp [D]
    rw [HD.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      (entranceRegion_radialDifferential_inverse hk hy hv.1).1,
      (entranceReturnState_fderiv_field hk hm hu hv hw).2, map_zero]
  have heq : entranceRadialDifferential y (entranceLogField y) =
      entranceRadialDrift y • Pi.single 0 1 + (y 1 * entranceStrongLogRate y) • Pi.single 1 1 +
        y 2 • Pi.single 2 1 + (y 3 * entranceWeakLogRate y) • Pi.single 3 1 := by
    rw [entranceRadialDifferential_logField hk hy hv.1]
    ext i
    fin_cases i <;> simp
  rw [heq, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul] at Hzero
  simp only [smul_eq_mul] at Hzero
  linarith only [Hzero]

end BianchiIX
