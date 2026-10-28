import BianchiIX.Analysis.ClockVariation
import BianchiIX.Dynamics.ExitCoordinateDifferential
import BianchiIX.Dynamics.ProjectiveFlowVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def exitClockProjection (y v : ProjectiveState) : ExitTailState :=
  fderiv ℝ toExitTailState y v -
    fderiv ℝ exitLogClock y v • exitTailField (y 2) (toExitTailState y)

def exitProjectedFlowVariation (y : ProjectiveState) (t₀ t : ℝ) (w : ProjectiveState) : ExitTailState :=
  exitClockProjection (projectiveOriginalFlow y t₀ t) (projectiveFlowDifferential y t₀ t w)

theorem hasDerivAt_exitClockProjection {β v : ℝ → ProjectiveState} {t : ℝ}
    (hβ : HasDerivAt β (projectiveOriginalField (β t)) t)
    (hv : HasDerivAt v (fderiv ℝ projectiveOriginalField (β t) (v t)) t)
    (hV : 0 < β t 2) (hm : β t 0 < 1) (hD : projectiveStateDenom (β t) ≠ 0)
    (hd : exitClockRate (β t) ≠ 0) :
    HasDerivAt (fun s => exitClockProjection (β s) (v s))
      (exitOriginalClockRate (β t) •
        fderiv ℝ (exitTailField (β t 2)) (toExitTailState (β t))
          (exitClockProjection (β t) (v t))) t := by
  have hVnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), 0 < y 2 :=
    (continuous_apply 2).continuousAt.eventually (isOpen_Ioi.mem_nhds hV)
  have hmnear : ∀ᶠ y : ProjectiveState in 𝓝 (β t), y 0 < 1 :=
    (show ContinuousAt (fun y : ProjectiveState => y 0) (β t) from
      (continuous_apply 0).continuousAt).eventually (isOpen_Iio.mem_nhds hm)
  have hdnear := (contDiff_exitClockRate 1).continuous.continuousAt.eventually_ne hd
  have hclock : (fun y => fderiv ℝ exitLogClock y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] exitOriginalClockRate := by
    filter_upwards [hVnear] with y hy
    exact exitLogClock_fderiv_field hy
  have hstate : (fun y => fderiv ℝ toExitTailState y (projectiveOriginalField y))
      =ᶠ[𝓝 (β t)] (fun y => exitOriginalClockRate y •
        exitTailField (Real.exp (-exitLogClock y)) (toExitTailState y)) := by
    filter_upwards [hVnear, hmnear, hdnear] with y hy hmy hdy
    rw [exp_neg_exitLogClock hy]
    exact toExitTailState_fderiv_field hy hmy hdy
  have hrad := coreRadius_pos (m := β t 0) hV
  have hvR : (β t 2) ^ 2 < coreRadius (β t 0) (β t 2) ^ 2 := by
    rw [coreRadius_sq]
    dsimp only [coreEnergy]
    nlinarith only [sq_pos_of_neg (sub_neg.mpr hm)]
  have hspeed : exitTailSpeed (coreRadius (β t 0) (β t 2)) (β t 1) (β t 2) (β t 3) ≠ 0 := by
    rwa [← exitClockRate_tail hm]
  have hfield : DifferentiableAt ℝ
      (fun q : ℝ × ExitTailState => exitTailField (Real.exp (-q.1)) q.2)
      (exitLogClock (β t), toExitTailState (β t)) := by
    have H := contDiffAt_exitTailField 1 (v := β t 2) (Y := toExitTailState (β t)) hvR hrad.ne' hspeed
    have hmap : ContDiffAt ℝ 1 (fun q : ℝ × ExitTailState => (Real.exp (-q.1), q.2))
        (exitLogClock (β t), toExitTailState (β t)) := by fun_prop
    have H' : ContDiffAt ℝ 1 (fun q : ℝ × ExitTailState => exitTailField q.1 q.2)
        (Real.exp (-exitLogClock (β t)), toExitTailState (β t)) := by
      simpa only [exp_neg_exitLogClock hV] using H
    have HC := H'.comp (f := fun q : ℝ × ExitTailState => (Real.exp (-q.1), q.2))
      (exitLogClock (β t), toExitTailState (β t)) hmap
    exact HC.differentiableAt (by norm_num)
  have H := hasDerivAt_coordinate_clock_variation
    (contDiffAt_toExitTailState 2 hV) (contDiffAt_exitLogClock 2 hV)
    ((contDiffAt_projectiveOriginalField 1 hD).differentiableAt (by norm_num))
    ((contDiffAt_exitOriginalClockRate 1 hD).differentiableAt (by norm_num))
    hfield hβ hv hclock hstate
  have heq : (fun s => fderiv ℝ toExitTailState (β s) (v s) -
      fderiv ℝ exitLogClock (β s) (v s) •
        exitTailField (Real.exp (-exitLogClock (β s))) (toExitTailState (β s)))
      =ᶠ[𝓝 t] (fun s => exitClockProjection (β s) (v s)) := by
    have hnear := ((continuous_apply 2).continuousAt.comp hβ.continuousAt).eventually
      (isOpen_Ioi.mem_nhds hV)
    filter_upwards [hnear] with s hs
    simp only [exp_neg_exitLogClock hs, exitClockProjection]
  simpa only [exp_neg_exitLogClock hV, exitClockProjection] using H.congr_of_eventuallyEq heq.symm

/-- The tangent is obtained from the actual Einstein flow, rather than postulated independently. -/
theorem hasDerivAt_exitProjectedFlowVariation {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hV : 0 < projectiveOriginalFlow y t₀ t 2) (hm : projectiveOriginalFlow y t₀ t 0 < 1)
    (hd : exitClockRate (projectiveOriginalFlow y t₀ t) ≠ 0) (w : ProjectiveState) :
    HasDerivAt (fun s => exitProjectedFlowVariation y t₀ s w)
      (exitOriginalClockRate (projectiveOriginalFlow y t₀ t) •
        fderiv ℝ (exitTailField (projectiveOriginalFlow y t₀ t 2))
          (toExitTailState (projectiveOriginalFlow y t₀ t))
            (exitProjectedFlowVariation y t₀ t w)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint hD.ne')
  exact hasDerivAt_exitClockProjection (hasDerivAt_projectiveOriginalFlow_time hD ht hA)
    (hasDerivAt_projectiveFlowDifferential_apply hD ht hA w) hV hm
    (toProjectiveState_denom_pos hA hc).ne' hd

theorem exitProjectedFlowVariation_initial {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) (w : ProjectiveState) :
    exitProjectedFlowVariation y t₀ t₀ w = exitClockProjection y w := by
  rw [exitProjectedFlowVariation, projectiveOriginalFlow_initial hD,
    projectiveFlowDifferential_initial hD, ContinuousLinearMap.id_apply]

end BianchiIX
