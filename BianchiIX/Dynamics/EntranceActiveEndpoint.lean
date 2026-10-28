import BianchiIX.Dynamics.EntranceRadialReturnDifferential
import BianchiIX.Dynamics.EntranceActiveVariation

noncomputable section

namespace BianchiIX

open Set

theorem entranceWallTangent_logField {y : ProjectiveState} (k : ℝ)
    (hu : y 1 ≠ 0) (hw : y 3 ≠ 0) (hD : entranceClockRate y ≠ 0) :
    entranceWallTangent k y (entranceLogField y) =
      ![entranceStrongLogRate y, k ^ 2 * entranceWeakLogRate y] := by
  obtain ⟨hU, hW⟩ := entranceLogField_wall_rates hD
  ext i
  fin_cases i <;> simp [entranceWallTangent, hU, hW, hu, hw]

/-- Differentiating the actual first arrival retains the terminal logarithmic growth rates. -/
theorem EntranceRadialInverseAt.return_logWalls_endpoint_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) (a : ℝ) (d : ProjectiveState) :
    fderiv ℝ (fun z => entranceLogWalls a (entranceReturnState (Ψ z)))
      (entranceRadialCoordinates y) d =
        entranceWallTangent a (entranceReturnState y)
          (entranceRadialClockVariation y 0 (entranceReturnTime y) d) -
        (d 2 / y 2) • ![entranceStrongLogRate (entranceReturnState y),
          a ^ 2 * entranceWeakLogRate (entranceReturnState y)] := by
  have HR := entranceReturn_regular hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have hpos := entranceReturn_walls_pos hk hm hu hv hw _ ht
  have hreg := entranceReturn_region hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ _ ht
  change 0 < entranceReturnState y 1 ∧ 0 < entranceReturnState y 2 ∧
    0 < entranceReturnState y 3 at hpos
  change entranceRegion (coreRadius (y 0) (y 2)) (entranceReturnState y) at hreg
  have hL := hasFDerivAt_entranceLogWalls a hpos.1.ne' hpos.2.2.ne'
  have hL' : HasFDerivAt (entranceLogWalls a)
      (fderiv ℝ (entranceLogWalls a) (entranceReturnState y))
      (entranceReturnState (Ψ (entranceRadialCoordinates y))) := by
    rw [HΨ.apply_base]
    exact hL.differentiableAt.hasFDerivAt
  have HD := hL'.comp (entranceRadialCoordinates y)
    (HΨ.hasFDerivAt_return hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩).differentiableAt.hasFDerivAt
  simp only [Function.comp_def] at HD
  rw [HD.fderiv, ContinuousLinearMap.comp_apply,
    HΨ.return_differential hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩, map_sub, map_smul,
    entranceLogWalls_fderiv_apply a hpos.1.ne' hpos.2.2.ne',
    entranceLogWalls_fderiv_apply a hpos.1.ne' hpos.2.2.ne',
    entranceWallTangent_logField a hpos.1.ne' hpos.2.2.ne'
      (entranceRegion_clock_pos hk hreg).ne']

/-- The active derivative in ordinary radial coordinates equals the fixed-clock response
after adding the exact correction for the moving exit. -/
theorem EntranceRadialInverseAt.return_active_endpoint {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) (a : ℝ) :
    let z := entranceRadialCoordinates y
    let Y := entranceReturnState y
    let v := entranceProjectedFlowVariation y 0 (entranceReturnTime y) (entranceActiveInitialVector y)
    let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
    let L := fun z => entranceLogWalls a (entranceReturnState (Ψ z))
    y 2 * fderiv ℝ Q z (Pi.single 2 1) + entranceRadialDrift Y =
        fderiv ℝ entranceStableRadius Y v ∧
      y 2 • fderiv ℝ L z (Pi.single 2 1) +
        ![entranceStrongLogRate Y, a ^ 2 * entranceWeakLogRate Y] = entranceWallTangent a Y v := by
  intro z Y v Q L
  have hd : (y 2 • (Pi.single 2 1 : ProjectiveState)) 2 / y 2 = 1 := by simp [hv.1.ne']
  have hR := HΨ.return_radius_differential hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
    (y 2 • Pi.single 2 1)
  have hL := HΨ.return_logWalls_endpoint_differential hk hm hu hv hw a (y 2 • Pi.single 2 1)
  rw [map_smul, hd, one_mul] at hR
  rw [map_smul, hd, one_smul] at hL
  constructor
  · change y 2 * fderiv ℝ Q z (Pi.single 2 1) =
      fderiv ℝ entranceStableRadius Y v - entranceRadialDrift Y at hR
    exact (eq_sub_iff_add_eq).mp hR
  · change y 2 • fderiv ℝ L z (Pi.single 2 1) =
      entranceWallTangent a Y v - ![entranceStrongLogRate Y, a ^ 2 * entranceWeakLogRate Y] at hL
    exact (eq_sub_iff_add_eq).mp hL

end BianchiIX
