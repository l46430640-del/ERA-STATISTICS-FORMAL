import BianchiIX.Dynamics.EntranceReturnMultipliers
import BianchiIX.Dynamics.EntranceRadialVariationBounds
import BianchiIX.Dynamics.EntranceRadialReturnDifferential

noncomputable section

namespace BianchiIX

open Set

def entranceLogMultiplierResponse (y : ProjectiveState) (i : Fin 3) : ProjectiveState →L[ℝ] ℝ :=
  (fderiv ℝ (fun z => Real.log (entranceReturnMultiplier z i)) y).comp
    (entranceRadialInverseDifferential y)

theorem continuousAt_entranceLogMultiplierResponse {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (i : Fin 3) (d : ProjectiveState) :
    ContinuousAt (fun z => entranceLogMultiplierResponse z i d) y := by
  have hy : entranceRegion (coreRadius (y 0) (y 2)) y :=
    ⟨hm, by simp; positivity, hu, ⟨hv.1.le, hv.2.le⟩, hw⟩
  exact ((entranceReturnMultiplier_regular hk hm hu hv hw i).2.1.continuousAt_fderiv
    (by norm_num)).clm_apply (continuousAt_entranceRadialInverseDifferential_apply hk hy hv.1 d)

theorem entranceReturn_logarithmic_differential {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (i : Fin 3) (hi : y i.succ ≠ 0) (v : ProjectiveState) :
    fderiv ℝ entranceReturnState y v i.succ / entranceReturnState y i.succ =
      v i.succ / y i.succ + fderiv ℝ (fun z => Real.log (entranceReturnMultiplier z i)) y v := by
  have hΛ := (entranceReturnMultiplier_regular hk hm hu hv hw i).1.differentiableAt (by norm_num)
  have hΛ0 := (entranceReturnMultiplier_pos y i).ne'
  have hl : fderiv ℝ (fun z => Real.log (entranceReturnMultiplier z i)) y v =
      fderiv ℝ (fun z => entranceReturnMultiplier z i) y v / entranceReturnMultiplier y i := by
    rw [(hΛ.hasFDerivAt.log hΛ0).fderiv]
    simp only [smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [entranceReturn_wall_differential hk hm hu hv hw,
    entranceReturn_wall_factorization (entrance_initial_denom_pos hk hm hu hv hw)
      (entranceReturn_regular hk hm hu hv hw).1, hl]
  field_simp

theorem EntranceRadialInverseAt.return_logWalls_multiplier {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) (d : ProjectiveState) :
    fderiv ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))) (entranceRadialCoordinates y) d =
      ![d 1 / y 1 + entranceLogMultiplierResponse y 0 d,
        d 3 / y 3 + entranceLogMultiplierResponse y 2 d] := by
  have hu' := And.intro hu.1.le hu.2
  have hw' := And.intro hw.1.le hw.2
  have HR := entranceReturn_regular hk hm hu' hv hw'
  have hpos := entranceReturn_walls_pos hk hm hu hv hw _ ⟨HR.1.1.1.1.le, le_rfl⟩
  change 0 < entranceReturnState y 1 ∧ 0 < entranceReturnState y 2 ∧ 0 < entranceReturnState y 3 at hpos
  have hL : HasFDerivAt (entranceLogWalls 1) (fderiv ℝ (entranceLogWalls 1) (entranceReturnState y))
      (entranceReturnState (Ψ (entranceRadialCoordinates y))) := by
    rw [HΨ.apply_base]
    exact (hasFDerivAt_entranceLogWalls 1 hpos.1.ne' hpos.2.2.ne').differentiableAt.hasFDerivAt
  have HD := hL.comp (entranceRadialCoordinates y)
    (f := fun z => entranceReturnState (Ψ z)) (HΨ.hasFDerivAt_return hk hm hu' hv hw')
  simp only [Function.comp_def] at HD
  rw [HD.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    entranceLogWalls_fderiv_apply 1 hpos.1.ne' hpos.2.2.ne']
  ext i
  fin_cases i
  · simpa [entranceWallTangent, entranceLogMultiplierResponse, entranceRadialInverseDifferential_apply] using
      entranceReturn_logarithmic_differential hk hm hu' hv hw' 0 hu.1.ne' (entranceRadialInverseDifferential y d)
  · simpa [entranceWallTangent, entranceLogMultiplierResponse, entranceRadialInverseDifferential_apply] using
      entranceReturn_logarithmic_differential hk hm hu' hv hw' 2 hw.1.ne' (entranceRadialInverseDifferential y d)

end BianchiIX
