import BianchiIX.Dynamics.CoreTailMultipliers

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Every valid downward tail, including signed walls, has the same smooth canonical arrival map. -/
theorem coreTail_regular_of_valid {Y : CoreAngleState} {η : ℝ}
    (hR : 1 < Y 0) (H : coreTailValid η Y) :
    ContDiffAt ℝ 2 (coreTailTime η) Y ∧ ContDiffAt ℝ 2 (coreTailState η) Y ∧
      (∀ᶠ Z in 𝓝 Y, coreTailValid η Z) := by
  let c : CoreAngleState → NormalizedState := fun Z => fromProjectiveState (coreTailEntry Z)
  have hD := coreTailValid_denom_pos H
  have hcc : ContDiffAt ℝ 2 c Y :=
    (contDiffAt_fromProjectiveState 2 hD.ne').comp Y (contDiffAt_coreTailEntry 2 hR)
  obtain ⟨τ, hτ, hcτ, hcP, _, hnear⟩ := exists_activeWall_first_downward_hit_two H.1.1.1
    H.2.1 H.2.2.2.1 H.1.1.2.2
  have hsmall : ∀ᶠ x in 𝓝 (c Y), ∀ t ∈ Icc 0 (τ x),
      |toProjectiveState (normalizedMaxCurve x 0 t) 3| < 1 / 2 := by
    apply eventually_forall_movingInterval hcτ.continuousAt (by rw [hτ]; exact H.1.1.1)
    intro t ht
    rw [hτ] at ht
    have hreg := H.2.1 t ht
    have hf := (normalizedMaxCurve_regular hreg.1).2.continuousAt
    have hp : ContinuousAt (fun q : NormalizedState × ℝ =>
        toProjectiveState (normalizedMaxCurve q.1 0 q.2)) (c Y, t) :=
      ContinuousAt.comp (g := toProjectiveState) (f := fun q : NormalizedState × ℝ => normalizedMaxCurve q.1 0 q.2)
        (contDiffAt_toProjectiveState 1 hreg.2.ne').continuousAt hf
    exact (continuousAt_pi.mp hp 3).abs.eventually (isOpen_Iio.mem_nhds (H.2.2.2.2 t ht))
  have hnear' := hcc.continuousAt.eventually hnear
  have hsmall' := hcc.continuousAt.eventually hsmall
  have heq : coreTailTime η =ᶠ[𝓝 Y] (fun Z => τ (c Z)) := by
    filter_upwards [hnear'] with Z hZ
    exact hZ.1.csInf_eq
  have hcTime : ContDiffAt ℝ 2 (coreTailTime η) Y :=
    (hcτ.comp Y hcc).congr_of_eventuallyEq heq
  have hcOut : ContDiffAt ℝ 2 (coreTailState η) Y := by
    have hcomp := hcP.comp Y hcc
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [heq] with Z hZ
    dsimp only [coreTailState, projectiveOriginalFlow]
    rw [hZ]
    rfl
  refine ⟨hcTime, hcOut, ?_⟩
  filter_upwards [heq, hnear', hsmall'] with Z hZ hfirst hsmallZ
  dsimp only [coreTailValid]
  rw [hZ]
  exact ⟨hfirst.1, hfirst.2.1, hfirst.2.2.1, hfirst.2.2.2, hsmallZ⟩

end BianchiIX
