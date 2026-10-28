import BianchiIX.Dynamics.StableResidualRateDecay
import BianchiIX.Analysis.ParametricDerivatives

noncomputable section

namespace BianchiIX

open Set

theorem contDiffAt_stableRescaledResidualRate_joint_two {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (fun p : ℝ × StableState => stableRescaledResidualRate (c + 1) p.1 p.2) (s, y) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidual_derivative_bounds
  obtain ⟨hM, hU, hW⟩ := stableRescaledFlow_band hc hm hu hw hs
  have hg := (HC c (stableRescaledFlow (c + 1) y s) hc hM hU hW).1
  have hp : ContDiffAt ℝ 2 (fun p : ℝ × StableState => (p.2, p.1)) (s, y) :=
    contDiffAt_snd.prodMk contDiffAt_fst
  have hflow := (contDiffAt_stableRescaledFlow_two (by linarith : 0 < c + 1) hc hm hu hw hs).comp (s, y) hp
  exact hg.comp (s, y) hflow

theorem continuousOn_stableRescaledResidualRate_derivatives {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    ContinuousOn (fun s => stableRescaledResidualRate (c + 1) s y) (Ici 0) ∧
      (∀ v, ContinuousOn (fun s => fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v) (Ici 0)) ∧
      (∀ v w, ContinuousOn (fun s => fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w) (Ici 0)) := by
  have h0 (s : ℝ) (hs : 0 ≤ s) := contDiffAt_stableRescaledResidualRate_joint_two hc hm hu hw hs
  have h1 (s : ℝ) (hs : 0 ≤ s) :
      ContDiffAt ℝ 1 (fun p : ℝ × StableState => fderiv ℝ (stableRescaledResidualRate (c + 1) p.1) p.2) (s, y) :=
    contDiffAt_partial_fderiv (h0 s hs) (by norm_num)
  have h2 (s : ℝ) (hs : 0 ≤ s) :
      ContDiffAt ℝ 0 (fun p : ℝ × StableState => fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) p.1)) p.2) (s, y) :=
    contDiffAt_partial_fderiv (h1 s hs) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact ((h0 s hs).continuousAt.comp (f := fun r : ℝ => (r, y))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  · intro v s hs
    exact (((h1 s hs).continuousAt.comp (f := fun r : ℝ => (r, y))
      (continuousAt_id.prodMk continuousAt_const)).clm_apply
      continuousAt_const).continuousWithinAt
  · intro v w s hs
    exact ((((h2 s hs).continuousAt.comp (f := fun r : ℝ => (r, y))
      (continuousAt_id.prodMk continuousAt_const)).clm_apply
      continuousAt_const).clm_apply continuousAt_const).continuousWithinAt

end BianchiIX
