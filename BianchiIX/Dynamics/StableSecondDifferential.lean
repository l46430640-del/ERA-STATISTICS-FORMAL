import BianchiIX.Dynamics.StableBoundaryRescaling
import BianchiIX.Dynamics.ProjectiveDifferentialRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableRescaledSecondDifferential (K : ℝ) (y : StableState) (s : ℝ) :
    StableState →L[ℝ] (StableState →L[ℝ] StableState) :=
  (fderiv ℝ (fun z : StableState × ℝ => stableRescaledDifferential K z.1 z.2) (y, s)).comp
    (ContinuousLinearMap.inl ℝ StableState ℝ)

theorem contDiffAt_stableRescaledDifferential_one {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 1 (fun z : StableState × ℝ => stableRescaledDifferential K z.1 z.2) (y, s) := by
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have ht := mul_nonneg hK.le hs
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint
    (fromProjectiveState_constraint hD.ne') 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have hp : ContDiffAt ℝ 1
      (fun z : StableState × ℝ => (stableInclusion z.1, K * z.2)) (y, s) :=
    (stableInclusion.contDiff.contDiffAt.comp (y, s) contDiffAt_fst).prodMk
      (contDiffAt_const.mul contDiffAt_snd)
  have H := (contDiffAt_projectiveFlowDifferential_one hD hdom hA).comp (y, s) hp
  exact contDiffAt_const.clm_comp (H.clm_comp contDiffAt_const)

theorem hasFDerivAt_stableRescaledDifferential {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasFDerivAt (fun z => stableRescaledDifferential K z s)
      (stableRescaledSecondDifferential K y s) y := by
  have H := ((contDiffAt_stableRescaledDifferential_one hK hc hm hu hw hs).differentiableAt
    (by norm_num)).hasFDerivAt
  exact H.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y s)

theorem continuousAt_stableRescaledSecondDifferential {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContinuousAt (fun z : StableState × ℝ => stableRescaledSecondDifferential K z.1 z.2) (y, s) :=
  ((contDiffAt_stableRescaledDifferential_one hK hc hm hu hw hs).continuousAt_fderiv
    (by norm_num)).clm_comp continuousAt_const

theorem stableRescaledSecondDifferential_initial {K : ℝ} {y : StableState} {c : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    stableRescaledSecondDifferential K y 0 = 0 := by
  have H := hasFDerivAt_stableRescaledDifferential hK hc hm hu hw (le_refl 0)
  simp only [stableRescaledDifferential_initial] at H
  exact H.unique (hasFDerivAt_const _ y)

end BianchiIX
