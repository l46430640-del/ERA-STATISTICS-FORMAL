import BianchiIX.Dynamics.StableProjectionFirstRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem stableBoundaryProjection_fderiv_eq {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y =
      stableCenterDifferentialLimit c y :=
  (hasFDerivAt_stableBoundaryProjection_in_band hc hm hu hw).fderiv

theorem stableBoundaryProjection_fderiv_drift {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (v : StableState) :
    |fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y v - v 0| ≤
      2 * stableVariationCenterBudget y v := by
  rw [stableBoundaryProjection_fderiv_eq hc hm hu hw]
  have heval : ContinuousAt (fun L : StableState →L[ℝ] ℝ => L v) (stableCenterDifferentialLimit c y) :=
    continuousAt_id.clm_apply continuousAt_const
  have H := heval.tendsto.comp (stableCenterDifferential_tendsto hc hm.le hu.le hw.le)
  apply le_of_tendsto ((H.sub_const (v 0)).abs)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  exact stableRescaledDifferential_center_drift hc hm.le hu.le hw.le hs v

theorem stableBoundaryProjection_fderiv_tail {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) :
    ‖fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y -
        stableCenterDifferential c y s‖ ≤ 2 * stableCenterTailCoefficient y * Real.exp (-s / 2) := by
  rw [stableBoundaryProjection_fderiv_eq hc hm hu hw]
  exact stableCenterDifferentialLimit_tail hc hm.le hu.le hw.le hs

theorem stableBoundaryProjection_fderiv_zero {m : ℝ} (hm : 2 ≤ m) :
    fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) ![m, 0, 0] =
      ContinuousLinearMap.proj 0 := by
  ext v
  have H := stableBoundaryProjection_fderiv_drift (y := ![m, 0, 0]) hm
    (by simp : |(![m, (0 : ℝ), 0] : StableState) 0 - m| < 1 / 40)
    (by change |(0 : ℝ)| < 1 / 200; norm_num) (by change |(0 : ℝ)| < 1 / 200; norm_num) v
  have H' : |fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) ![m, 0, 0] v - v 0| ≤ 0 := by
    simpa [stableVariationCenterBudget] using H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H' (abs_nonneg _)))

theorem stableBoundaryProjection_annihilates_field {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y
      (stableBoundaryField y) = 0 := by
  let p := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  have hd : HasFDerivAt p (fderiv ℝ p y) y :=
    ((contDiffAt_stableBoundaryProjection_one hm hu hw).differentiableAt (by norm_num)).hasFDerivAt
  have hflow : HasDerivAt (stableOriginalFlow y) (stableOriginalField y) 0 := by
    simpa only [stableOriginalFlow_initial] using hasDerivAt_stableOriginalFlow hm
      (by simp : |y 0 - y 0| ≤ (1 : ℝ) / 40) hu.le hw.le (le_refl 0)
  have hd' : HasFDerivAt p (fderiv ℝ p y) (stableOriginalFlow y 0) := by
    rw [stableOriginalFlow_initial]
    exact hd
  have H := hd'.comp_hasDerivAt 0 hflow
  have heq (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) : p (stableOriginalFlow y t) = p y := by
    simp only [p, stableOriginalFlow_eq, stableRestriction_apply]
    exact stableBoundaryProjection_invariant hm (by simp : |y 0 - y 0| ≤ (1 : ℝ) / 40) hu.le hw.le ht
  have hconst : HasDerivWithinAt (fun t => p (stableOriginalFlow y t)) 0 (Ici 0) 0 :=
    (hasDerivWithinAt_const 0 (Ici 0) (p y)).congr_of_mem heq (by simp)
  have hzero : fderiv ℝ p y (stableOriginalField y) = 0 :=
    (H.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
      (hconst.derivWithin (uniqueDiffWithinAt_Ici 0))
  rw [stableOriginalField, map_smul, smul_eq_mul] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left
    (div_ne_zero (by norm_num) (stableBoundaryDenom_pos y).ne')

end BianchiIX
