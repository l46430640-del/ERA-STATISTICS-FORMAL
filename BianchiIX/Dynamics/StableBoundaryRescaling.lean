import BianchiIX.Dynamics.StableBoundaryLinearization

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- The scale is held fixed when differentiating the initial state. -/
def stableRescaledFlow (K : ℝ) (y : StableState) (s : ℝ) : StableState :=
  stableOriginalFlow y (K * s)

def stableRescaledDifferential (K : ℝ) (y : StableState) (s : ℝ) : StableState →L[ℝ] StableState :=
  stableFlowDifferential y (K * s)

theorem stableRescaledFlow_initial (K : ℝ) (y : StableState) : stableRescaledFlow K y 0 = y := by
  simp only [stableRescaledFlow, mul_zero, stableOriginalFlow_initial]

theorem stableRescaledDifferential_initial (K : ℝ) (y : StableState) :
    stableRescaledDifferential K y 0 = ContinuousLinearMap.id ℝ StableState := by
  simp only [stableRescaledDifferential, mul_zero, stableFlowDifferential_initial]

theorem hasDerivAt_stableRescaledFlow {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasDerivAt (stableRescaledFlow K y) (K • stableOriginalField (stableRescaledFlow K y s)) s := by
  exact (hasDerivAt_stableOriginalFlow hc hm hu hw (mul_nonneg hK.le hs)).scomp s
    (by simpa using (hasDerivAt_id s).const_mul K)

theorem hasFDerivAt_stableRescaledFlow {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasFDerivAt (fun z => stableRescaledFlow K z s) (stableRescaledDifferential K y s) y :=
  hasFDerivAt_stableOriginalFlow hc hm hu hw (mul_nonneg hK.le hs)

theorem stableRescaledFlow_variational_equation {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) (v : StableState) :
    HasDerivAt (fun r => stableRescaledDifferential K y r v)
      (K • (stableOriginalJacobian (stableRescaledFlow K y s)).mulVec
        (stableRescaledDifferential K y s v)) s := by
  exact (stableFlow_variational_equation hc hm hu hw (mul_nonneg hK.le hs) v).scomp s
    (by simpa using (hasDerivAt_id s).const_mul K)

theorem contDiffAt_stableOriginalFlow_two {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (fun z : StableState × ℝ => stableOriginalFlow z.1 z.2) (y, t) := by
  simp_rw [stableOriginalFlow_eq]
  exact stableRestriction.contDiff.contDiffAt.comp (y, t)
    (contDiffAt_stableBoundaryOrbit_two hc hm hu hw ht)

theorem contDiffAt_stableRescaledFlow_two {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (fun z : StableState × ℝ => stableRescaledFlow K z.1 z.2) (y, s) := by
  have H := contDiffAt_stableOriginalFlow_two hc hm hu hw (mul_nonneg hK.le hs)
  have hmap : ContDiffAt ℝ 2 (fun z : StableState × ℝ => (z.1, K * z.2)) (y, s) :=
    contDiffAt_fst.prodMk (contDiffAt_const.mul contDiffAt_snd)
  have H' := H.comp (y, s) hmap
  exact H'

theorem stableOriginalFlow_limit {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Tendsto (stableOriginalFlow y) atTop (𝓝 ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) := by
  have H := stableBoundaryProjection_exists hc hm hu hw
  apply tendsto_pi_nhds.mpr
  intro i
  simp_rw [stableOriginalFlow_eq, stableRestriction_apply]
  fin_cases i
  · exact H.1
  · exact H.2.1
  · exact H.2.2.1

theorem stableRescaledFlow_limit {K : ℝ} {y : StableState} {c : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Tendsto (stableRescaledFlow K y) atTop (𝓝 ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) :=
  (stableOriginalFlow_limit hc hm hu hw).comp (Tendsto.const_mul_atTop hK tendsto_id)

end BianchiIX
