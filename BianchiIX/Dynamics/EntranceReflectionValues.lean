import BianchiIX.Dynamics.EntranceFullCoreIdentification
import BianchiIX.Dynamics.CoreReflection

noncomputable section

namespace BianchiIX

open Set

/-- The same full reflection after a preceding entrance loses between one and three radius units. -/
theorem entrancePartialCore_reflection_values {y : ProjectiveState} {η : ℝ}
    (hk : 8 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 10000)
    (hsmall : y 1 + y 2 * y 3 ≤ η / (2 * coreRadius (y 0) (y 2))) :
    let z := entranceReturnState y
    let κ := coreRadius (z 0) (z 2)
    let p := coreExitConnectionParameters (partialCoreDownwardReturnState y)
    let G := connectionReturnPhysicalState p
    κ / 2 ≤ p 0 ∧ (1 ≤ κ - G 0 ∧ κ - G 0 ≤ 3) ∧ κ / 2 ≤ G 0 ∧ G 0 ≤ κ ∧
      |G 0 - (κ - 2)| ≤ 64 * (z 1 + (z 3) ^ 2) / κ ∧
      (0 < G 1 ∧ G 1 ≤ z 1) ∧ (0 < G 2 ∧ G 2 ≤ z 3) := by
  intro z κ p G
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
  have HE := entranceReturn_regular hk' hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  obtain ⟨hκ, _, hhit, _, _, _, _, hsum, _⟩ :=
    entranceReturn_partialCore_entry hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ hη hsmall
  have HP := entranceReturn_walls_pos hk' hm hu hv hw _ ⟨HE.1.1.1.1.le, le_rfl⟩
  change 0 < z 1 ∧ 0 < z 2 ∧ 0 < z 3 at HP
  change z 2 = 1 at hhit
  let X := toCoreAngleState z
  have hκ0 : 0 ≤ κ := by change 6 ≤ κ at hκ; linarith only [hκ]
  have hUX : 0 < X 1 := HP.1
  have hWX : 0 < X 2 := mul_pos HP.2.1 HP.2.2
  have hsum' : X 1 + X 2 ≤ (1 / 10000) / X 0 :=
    hsum.trans (div_le_div_of_nonneg_right hη.2 hκ0)
  have huX : 0 < X 1 ∧ X 1 ≤ (1 / 10000) / X 0 :=
    ⟨hUX, (le_add_of_nonneg_right hWX.le).trans hsum'⟩
  have hwX : 0 < X 2 ∧ X 2 ≤ (1 / 10000) / X 0 :=
    ⟨hWX, (le_add_of_nonneg_left hUX.le).trans hsum'⟩
  have hfirst := (coreRadiusReturn_large_regular hκ ⟨huX.1.le, huX.2⟩ ⟨hwX.1.le, hwX.2⟩).2.2.2.self_of_nhds
  have H := coreReflection_actual_step hκ huX hwX hfirst
  have Hdata := coreReturn_connection_data hκ huX hwX hfirst
  have hstate := (entrancePartialCore_fullCore_eventuallyEq hk hm ⟨hu.1.le, hu.2⟩ hv
    ⟨hw.1.le, hw.2⟩ hη hsmall).2.self_of_nhds
  have hp : p = coreConnectionParameters coreRadiusReturnTime X := congrArg coreExitConnectionParameters hstate
  have hG : G = coreReflectionState coreRadiusReturnTime X := congrArg connectionReturnPhysicalState hp
  have hdrop : 1 ≤ κ - G 0 ∧ κ - G 0 ≤ 3 := by rw [hG]; exact H.2.2.2.2.2.2
  refine ⟨?_, hdrop, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp]
    exact Hdata.2.1.2.1
  · change 6 ≤ κ at hκ
    linarith only [hκ, hdrop.2]
  · linarith only [hdrop.1]
  · rw [hG]
    have HV := H.2.2.2.1
    change |coreReflectionState coreRadiusReturnTime X 0 - (κ - 2)| ≤
      64 * (z 1 + (z 2 * z 3) ^ 2) / κ at HV
    simpa only [hhit, one_mul] using HV
  · rw [hG]
    exact H.2.2.2.2.1
  · rw [hG]
    have HW := H.2.2.2.2.2.1
    change 0 < coreReflectionState coreRadiusReturnTime X 2 ∧
      coreReflectionState coreRadiusReturnTime X 2 ≤ z 2 * z 3 at HW
    simpa only [hhit, one_mul] using HW

end BianchiIX
