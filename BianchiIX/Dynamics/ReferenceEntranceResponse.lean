import BianchiIX.Dynamics.ReferenceEntrance
import BianchiIX.Dynamics.ReferenceRadiusResponse
import BianchiIX.Dynamics.EntranceRadialReturnDifferential

noncomputable section

namespace BianchiIX

def referenceEntranceDuration (k v : ℝ) : ℝ := referenceHeightTime k v - referenceHalfTime k

def referenceEntranceStrongResponse (k v : ℝ) : ℝ :=
  -2 * v / k * (1 - Real.exp (-(k ^ 2 / 2) * referenceEntranceDuration k v))

theorem referenceEntranceDuration_eq (k v : ℝ) :
    referenceEntranceDuration k v = (Real.arcosh (k / v) - Real.arcosh k) / k := by
  dsimp [referenceEntranceDuration, referenceHeightTime, referenceHalfTime]
  ring

theorem referenceEntranceStrongResponse_eq (k v : ℝ) :
    referenceEntranceStrongResponse k v = -2 * v / k *
      (1 - Real.exp (-(k ^ 2 / 2) * ((Real.arcosh (k / v) - Real.arcosh k) / k))) := by
  rw [referenceEntranceStrongResponse, referenceEntranceDuration_eq]

theorem referenceEntrance_physical_strong_derivative {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    fderiv ℝ (fun y : ProjectiveState => coreRadius (entranceReturnState y 0) (entranceReturnState y 2))
      (referenceEntranceState k v) (Pi.single 1 1) = referenceEntranceStrongResponse k v := by
  let y := referenceEntranceState k v
  let s := -referenceHeightTime k v
  let t := -referenceHalfTime k
  let R := fun y : ProjectiveState => coreRadius (y 0) (y 2)
  have hk0 : 0 < k := by linarith
  have hentry : referencePulse k s = y := referencePulse_height_entry hk0 ⟨hv.1, by linarith [hv.2]⟩
  have hR : coreRadius (y 0) (y 2) = k := referenceEntrance_radius hk0 ⟨hv.1, by linarith [hv.2]⟩
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by rw [hR]; exact hk
  have hm : 1 ≤ y 0 := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hret := referenceEntrance_return hk hv
  have hV : 0 < entranceReturnState y 2 := by rw [hret.2]; exact referencePulse_active_pos hk0 t
  have hRder := (hasFDerivAt_coreRadius_state hV).differentiableAt.hasFDerivAt
  have hd := hRder.comp y ((entranceReturn_regular hk' hm hu hv hw).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  have hevent := (entranceReturn_differential hk' hm hu hv hw (Pi.single 1 1)).2
  simp only [Function.comp_def] at hd
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, hevent, map_sub, map_smul,
    hret.2, referencePulse_radius_field hk0, smul_zero, sub_zero, hret.1]
  have H := referenceShiftedVariation_radius hk0 s t (Pi.single 1 1)
  dsimp only at H
  change fderiv ℝ R (referencePulse k t) (referenceShiftedVariation k s (Pi.single 1 1) t) =
    fderiv ℝ R (referencePulse k s) (Pi.single 1 1) + _ at H
  have hzero : fderiv ℝ R (referencePulse k s) (Pi.single 1 1) = 0 := by
    rw [referencePulse_radius_fderiv hk0]
    simp
  have hvs : referencePulse k s 2 = v := by rw [hentry]; rfl
  rw [hzero, zero_add, hvs] at H
  simp only [Pi.single_eq_same, mul_one] at H
  rw [← hentry]
  change fderiv ℝ R (referencePulse k t) (referenceShiftedVariation k s (Pi.single 1 1) t) = _
  rw [H]
  have htime : t - s = referenceEntranceDuration k v := by dsimp [s, t, referenceEntranceDuration]; ring
  rw [htime]
  dsimp [referenceEntranceStrongResponse]
  ring

theorem entranceRadialInverseDifferential_strong_zero {m v : ℝ} (hm : 2 ≤ m) :
    entranceRadialInverseDifferential ![m, 0, v, 0] (Pi.single 1 1) = Pi.single 1 1 := by
  have hp : entranceStablePartial ![m, 0, v, 0] 1 = 0 := by
    rw [entranceStablePartial, entranceStablePhase_fderiv hm
      (by change |(0 : ℝ)| < 1 / 200; norm_num) (by change |(0 : ℝ)| < 1 / 200; norm_num)]
    have hs : stableRestriction (![m, 0, v, 0] : ProjectiveState) = ![m, 0, 0] := by
      ext i
      fin_cases i <;> simp [stableRestriction]
    have hd : stableRestriction (Pi.single (1 : Fin 4) (1 : ℝ)) = ![0, 1, 0] := by
      ext i
      fin_cases i <;> simp [stableRestriction]
    rw [hs, hd, stableBoundaryProjection_fderiv_zero hm]
    rfl
  rw [entranceRadialInverseDifferential_apply]
  ext i
  fin_cases i <;> simp [hp]

theorem referenceEntrance_radialCoordinates {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    entranceRadialCoordinates (referenceEntranceState k v) = ![k, 0, v, 0] := by
  let y := referenceEntranceState k v
  have hk0 : 0 < k := by linarith
  have hR : coreRadius (y 0) (y 2) = k := referenceEntrance_radius hk0 ⟨hv.1, by linarith [hv.2]⟩
  have hy : entranceRegion k y := ⟨le_add_of_nonneg_right (Real.sqrt_nonneg _),
    by rw [hR, sub_self, abs_zero]; linarith,
    by dsimp [y, referenceEntranceState]; norm_num,
    ⟨hv.1.le, hv.2.le⟩, by dsimp [y, referenceEntranceState]; norm_num⟩
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hp : entranceStablePhase y = y 0 := stableBoundaryProjection_zero hm
  have hr : entranceStableRadius y = k := by
    change coreRadius (entranceStablePhase y) (y 2) = k
    rw [hp, hR]
  change ![entranceStableRadius y, 0, v, 0] = ![k, 0, v, 0]
  rw [hr]

/-- Equation (C.46) is the derivative of the actual first-arrival physical radius
in ordinary corrected radial coordinates, at the zero stable-wall boundary. -/
theorem EntranceRadialInverseAt.referenceEntrance_strong_derivative {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    fderiv ℝ (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
      ![k, 0, v, 0] (Pi.single 1 1) =
        referenceEntranceStrongResponse k v := by
  rw [← referenceEntrance_radialCoordinates hk hv]
  let y := referenceEntranceState k v
  let F := fun y : ProjectiveState => coreRadius (entranceReturnState y 0) (entranceReturnState y 2)
  have hk0 : 0 < k := by linarith
  have hR : coreRadius (y 0) (y 2) = k := referenceEntrance_radius hk0 ⟨hv.1, by linarith [hv.2]⟩
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by rw [hR]; exact hk
  have hm : 1 ≤ y 0 := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hy : entranceRegion k y := ⟨hm, by rw [hR, sub_self, abs_zero]; linarith,
    hu, ⟨hv.1.le, hv.2.le⟩, hw⟩
  have hm2 : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hV : 0 < entranceReturnState y 2 := by rw [(entranceReturn_active_component hk' hm hu hv hw).1]; norm_num
  have hF : DifferentiableAt ℝ F y := (hasFDerivAt_coreRadius_state hV).differentiableAt.comp y
    ((entranceReturn_regular hk' hm hu hv hw).2.2.1.differentiableAt (by norm_num))
  have hinv : entranceRadialInverseDifferential y (Pi.single 1 1) = Pi.single 1 1 :=
    entranceRadialInverseDifferential_strong_zero (v := v) hm2
  rw [HΨ.scalar_differential hF]
  change fderiv ℝ F y (entranceRadialInverseDifferential y (Pi.single 1 1)) = _
  rw [hinv]
  exact referenceEntrance_physical_strong_derivative hk hv

end BianchiIX
