import BianchiIX.Dynamics.EntranceActiveVariation
import BianchiIX.Dynamics.EntranceReturnSegment

noncomputable section

namespace BianchiIX

open Set

/-- Equation (C.43) with zero initial data on the whole actual first-arrival segment. -/
theorem entrance_return_active_variation_system {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) :
    let k := coreRadius (y 0) (y 2)
    let Y := projectiveOriginalFlow y 0
    let v := fun t => entranceProjectedFlowVariation y 0 t (entranceActiveInitialVector y)
    let Z := fun t => fderiv ℝ entranceStableRadius (Y t) (v t)
    let f := fun t => entranceWallTangent k (Y t) (v t)
    Z 0 = 0 ∧ f 0 = 0 ∧ ∀ t ∈ Icc 0 (entranceReturnTime y),
      let c := entranceRadialVariationCoefficients (Y t)
      let q := entranceOriginalClockRate (Y t)
      HasDerivAt Z (q * (c 0 * Z t + c 1 * (v t 1 / Y t 1) + c 2 * (v t 3 / Y t 3) +
        entrancePhaseActiveSource (Y t))) t ∧
      HasDerivAt f (q • ((entranceWallWeightedMatrix k (Y t)).mulVec (f t) +
        Z t • entranceWallRadialSource k (Y t) + entranceWallActiveSource k (Y t))) t := by
  intro k Y v Z f
  have hD := entrance_initial_denom_pos hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  have HR := (entranceReturn_regular hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩).1
  have hreg := entranceReturn_region hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  have hpos := entranceReturn_walls_pos hk hm hu hv hw
  have hy : entranceRegion k y := by
    simpa only [projectiveOriginalFlow_initial hD] using hreg 0 ⟨le_rfl, HR.1.1.1.le⟩
  obtain ⟨hZ, hf, hζ⟩ := entranceActiveVariation_initial hD hk hy hv.1 0
  refine ⟨hZ, hf, fun t ht => ?_⟩
  have Hp := hpos t ht
  have H := hasDerivAt_entranceProjectedForcedTangents hD (HR.2.1 t ht).1 (HR.2.1 t ht).2
    hk (hreg t ht) Hp.2.1 Hp.1.ne' Hp.2.2.ne' (entranceActiveInitialVector y)
  simpa only [hζ, one_mul, one_smul] using H

end BianchiIX
