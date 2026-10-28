import BianchiIX.Dynamics.StableCenterSecondLimit
import BianchiIX.Dynamics.StableProjectionDifferential

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem contDiffAt_stableBoundaryProjection_two_in_band {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 2 (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y := by
  change ContDiffAt ℝ ((1 : ℕ) + 1) _ y
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨stableCenterDifferentialLimit c, ⟨stableParameterDomain c,
    (isOpen_stableParameterDomain c).mem_nhds ⟨hm, hu, hw⟩, ?_⟩,
    contDiffAt_stableCenterDifferentialLimit_one hc hm hu hw⟩
  intro z hz
  exact hasFDerivAt_stableBoundaryProjection_in_band hc hz.1 hz.2.1 hz.2.2

theorem contDiffAt_stableBoundaryProjection_two {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 2 (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y :=
  contDiffAt_stableBoundaryProjection_two_in_band hm (by simp) hu hw

theorem hasFDerivAt_stableBoundaryProjection_fderiv {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    HasFDerivAt (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)))
      (stableCenterSecondDifferentialLimit c y) y := by
  apply (hasFDerivAt_stableCenterDifferentialLimit hc hm hu hw).congr_of_eventuallyEq
  filter_upwards [(isOpen_stableParameterDomain c).mem_nhds ⟨hm, hu, hw⟩] with z hz
  exact stableBoundaryProjection_fderiv_eq hc hz.1 hz.2.1 hz.2.2

theorem stableBoundaryProjection_fderiv2_eq {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))) y =
      stableCenterSecondDifferentialLimit c y :=
  (hasFDerivAt_stableBoundaryProjection_fderiv hc hm hu hw).fderiv

theorem stableBoundaryProjection_fderiv2_tail {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) :
    ‖fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))) y -
        stableCenterSecondDifferential c y s‖ ≤
      4 * stableSecondCenterBudget y * Real.exp (-s / 4) := by
  rw [stableBoundaryProjection_fderiv2_eq hc hm hu hw]
  exact stableCenterSecondDifferentialLimit_tail hc hm hu hw hs

theorem stableBoundaryProjection_fderiv2_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ‖fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))) y‖ ≤
      40000 * Real.exp (512 * (|y 1| + |y 2|)) ^ 3 := by
  rw [stableBoundaryProjection_fderiv2_eq hc hm hu hw]
  have hnorm : Tendsto (fun s : ℝ => ‖stableCenterSecondDifferential c y s‖) atTop
      (𝓝 ‖stableCenterSecondDifferentialLimit c y‖) :=
    Tendsto.norm (E := StableState →L[ℝ] (StableState →L[ℝ] ℝ))
      (stableCenterSecondDifferential_tendsto hc hm hu hw)
  apply le_of_tendsto hnorm
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  change |stableRescaledSecondDifferential (c + 1) y s v w 0| ≤ _
  exact (show |stableRescaledSecondDifferential (c + 1) y s v w 0| ≤
      ‖stableRescaledSecondDifferential (c + 1) y s v w‖ by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (stableRescaledSecondDifferential (c + 1) y s v w) 0).trans
    (stableRescaledSecondDifferential_bound hc hm hu hw hs v w)

theorem stableCenterSecondDifferentialLimit_independent {y : StableState} {c d : ℝ}
    (hc : 2 ≤ c) (hd : 2 ≤ d) (hmc : |y 0 - c| < 1 / 40) (hmd : |y 0 - d| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    stableCenterSecondDifferentialLimit c y = stableCenterSecondDifferentialLimit d y :=
  (hasFDerivAt_stableBoundaryProjection_fderiv hc hmc hu hw).unique
    (hasFDerivAt_stableBoundaryProjection_fderiv hd hmd hu hw)

theorem stableBoundaryProjection_fderiv2_symm {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))) y v w =
      fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))) y w v :=
  ((contDiffAt_stableBoundaryProjection_two_in_band hc hm hu hw).isSymmSndFDerivAt (by norm_num)).eq v w

end BianchiIX
