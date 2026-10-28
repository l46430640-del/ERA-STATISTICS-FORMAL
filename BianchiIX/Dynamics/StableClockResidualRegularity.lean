import BianchiIX.Dynamics.StableClockResidualDecay
import BianchiIX.Analysis.ParametricDerivatives

noncomputable section

namespace BianchiIX

open Set

theorem contDiffAt_stableClockResidualRate_joint_two {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (fun p : ℝ × StableState => stableClockResidualRate c p.1 p.2) (s, y) :=
  (contDiffAt_stableClockResidual_two hc hy hs).comp (s, y)
    (g := stableClockResidual c) (f := fun p : ℝ × StableState => (p.2, p.1))
    (contDiffAt_snd.prodMk contDiffAt_fst)

theorem continuousOn_stableClockResidualRate_derivatives {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) :
    ContinuousOn (fun s => stableClockResidualRate c s y) (Ici 0) ∧
      (∀ v, ContinuousOn (fun s => fderiv ℝ (stableClockResidualRate c s) y v) (Ici 0)) ∧
      (∀ v w, ContinuousOn (fun s => fderiv ℝ (fderiv ℝ (stableClockResidualRate c s)) y v w) (Ici 0)) := by
  have h0 (s : ℝ) (hs : 0 ≤ s) := contDiffAt_stableClockResidualRate_joint_two hc hy hs
  have h1 (s : ℝ) (hs : 0 ≤ s) :
      ContDiffAt ℝ 1 (fun p : ℝ × StableState => fderiv ℝ (stableClockResidualRate c p.1) p.2) (s, y) :=
    contDiffAt_partial_fderiv (h0 s hs) (by norm_num)
  have h2 (s : ℝ) (hs : 0 ≤ s) :
      ContDiffAt ℝ 0 (fun p : ℝ × StableState => fderiv ℝ (fderiv ℝ (stableClockResidualRate c p.1)) p.2) (s, y) :=
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
