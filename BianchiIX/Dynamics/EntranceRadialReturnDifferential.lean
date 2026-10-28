import BianchiIX.Dynamics.EntranceReturnSegment
import BianchiIX.Dynamics.EntranceRadialVariation
import BianchiIX.Dynamics.EntranceActualWallResponse

noncomputable section

namespace BianchiIX

open Set

def entranceRadialClockVariation (y : ProjectiveState) (t₀ t : ℝ) (d : ProjectiveState) : ProjectiveState :=
  entranceProjectedFlowVariation y t₀ t (entranceRadialInverseDifferential y d)

theorem entranceRegion_radialDifferential_inverse {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    Function.LeftInverse (entranceRadialInverseDifferential y) (entranceRadialDifferential y) ∧
      Function.RightInverse (entranceRadialInverseDifferential y) (entranceRadialDifferential y) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  exact entranceRadialDifferential_inverse hm hu hw hv (by linarith [hchi.1]) (by linarith [hPM.1])

theorem entranceRadialInverseDifferential_radius {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (d : ProjectiveState) :
    fderiv ℝ entranceStableRadius y (entranceRadialInverseDifferential y d) = d 0 := by
  have H := (entranceRegion_radialDifferential_inverse hk hy hv).2 d
  exact congrArg (fun z : ProjectiveState => z 0) H

theorem entranceRadialClockVariation_initial {y : ProjectiveState} {k : ℝ}
    (hD : 0 < projectiveStateDenom y) (hk : 7 / 4 ≤ k) (hy : entranceRegion k y)
    (hv : 0 < y 2) (t₀ : ℝ) (d : ProjectiveState) :
    fderiv ℝ entranceStableRadius y (entranceRadialClockVariation y t₀ t₀ d) = d 0 ∧
      entranceRadialClockVariation y t₀ t₀ d 1 = d 1 ∧
      entranceRadialClockVariation y t₀ t₀ d 2 = d 2 ∧
      entranceRadialClockVariation y t₀ t₀ d 3 = d 3 := by
  simp only [entranceRadialClockVariation, entranceProjectedFlowVariation_initial hD]
  refine ⟨entranceRadialInverseDifferential_radius hk hy hv d, ?_⟩
  simp [entranceRadialInverseDifferential_apply]

theorem EntranceRadialInverseAt.hasFDerivAt_return {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    HasFDerivAt (fun z => entranceReturnState (Ψ z))
      ((fderiv ℝ entranceReturnState y).comp (entranceRadialInverseDifferential y)) (entranceRadialCoordinates y) := by
  have hd : HasFDerivAt entranceReturnState (fderiv ℝ entranceReturnState y) (Ψ (entranceRadialCoordinates y)) := by
    rw [HΨ.apply_base]
    exact ((entranceReturn_regular hk hm hu hv hw).2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  simpa only [Function.comp_def] using hd.comp (entranceRadialCoordinates y) HΨ.hasFDerivAt

/-- Ordinary radial coordinates retain the exact correction for a moving active-wall endpoint. -/
theorem EntranceRadialInverseAt.return_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (d : ProjectiveState) :
    fderiv ℝ (fun z => entranceReturnState (Ψ z)) (entranceRadialCoordinates y) d =
      entranceRadialClockVariation y 0 (entranceReturnTime y) d -
        (d 2 / y 2) • entranceLogField (entranceReturnState y) := by
  rw [(HΨ.hasFDerivAt_return hk hm hu hv hw).fderiv, ContinuousLinearMap.comp_apply,
    entranceReturn_clock_differential hk hm hu hv hw]
  congr 2

theorem EntranceRadialInverseAt.return_radius_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (d : ProjectiveState) :
    fderiv ℝ (fun z => entranceStableRadius (entranceReturnState (Ψ z))) (entranceRadialCoordinates y) d =
      fderiv ℝ entranceStableRadius (entranceReturnState y) (entranceRadialClockVariation y 0 (entranceReturnTime y) d) -
        (d 2 / y 2) * entranceRadialDrift (entranceReturnState y) := by
  have HR := entranceReturn_regular hk hm hu hv hw
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have hy := entranceReturn_region hk hm hu hv hw _ ht
  change entranceRegion (coreRadius (y 0) (y 2)) (entranceReturnState y) at hy
  have hhit := (entranceReturn_active_component hk hm hu hv hw).1
  have hv' : 0 < entranceReturnState y 2 := by rw [hhit]; norm_num
  have hm' : 2 ≤ entranceReturnState y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu' : |entranceReturnState y 1| < 1 / 200 := by
    rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw' : |entranceReturnState y 3| < 1 / 200 := by
    rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hR := ((contDiffAt_entranceStableRadius_two hm' hu' hw' hv').differentiableAt (by norm_num)).hasFDerivAt
  have hd := (HΨ.hasFDerivAt_return hk hm hu hv hw).differentiableAt
  have hR' : HasFDerivAt entranceStableRadius (fderiv ℝ entranceStableRadius (entranceReturnState y))
      (entranceReturnState (Ψ (entranceRadialCoordinates y))) := by simpa only [HΨ.apply_base] using hR
  have HD := hR'.comp (entranceRadialCoordinates y) hd.hasFDerivAt
  simp only [Function.comp_def] at HD
  rw [HD.fderiv, ContinuousLinearMap.comp_apply,
    HΨ.return_differential hk hm hu hv hw, map_sub, map_smul]
  have HE : fderiv ℝ entranceStableRadius (entranceReturnState y) (entranceLogField (entranceReturnState y)) =
      entranceRadialDrift (entranceReturnState y) := (entranceRadialDrift_lie_eventuallyEq hk hy hv').self_of_nhds
  rw [HE, smul_eq_mul]

theorem EntranceRadialInverseAt.return_logWalls_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) (d : ProjectiveState) (hd2 : d 2 = 0) :
    fderiv ℝ (fun z => entranceLogWalls (coreRadius (y 0) (y 2)) (entranceReturnState (Ψ z)))
      (entranceRadialCoordinates y) d =
        entranceWallTangent (coreRadius (y 0) (y 2)) (entranceReturnState y)
          (entranceRadialClockVariation y 0 (entranceReturnTime y) d) := by
  have HR := entranceReturn_regular hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have hpos := entranceReturn_walls_pos hk hm hu hv hw _ ht
  have hL := hasFDerivAt_entranceLogWalls (coreRadius (y 0) (y 2)) hpos.1.ne' hpos.2.2.ne'
  have hd := (HΨ.hasFDerivAt_return hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩).differentiableAt
  have hL' : HasFDerivAt (entranceLogWalls (coreRadius (y 0) (y 2)))
      (fderiv ℝ (entranceLogWalls (coreRadius (y 0) (y 2))) (entranceReturnState y))
      (entranceReturnState (Ψ (entranceRadialCoordinates y))) := by
    rw [HΨ.apply_base]
    exact hL.differentiableAt.hasFDerivAt
  have HD := hL'.comp (entranceRadialCoordinates y) hd.hasFDerivAt
  simp only [Function.comp_def] at HD
  rw [HD.fderiv, ContinuousLinearMap.comp_apply,
    HΨ.return_differential hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩, hd2, zero_div, zero_smul, sub_zero]
  exact entranceLogWalls_fderiv_apply _ hpos.1.ne' hpos.2.2.ne' _

end BianchiIX
