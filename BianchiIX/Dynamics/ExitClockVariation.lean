import BianchiIX.Dynamics.ExitClockFlow
import BianchiIX.Analysis.ParametricVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem contDiffAt_exitClockField {y : ProjectiveState} (hV : 0 < y 2) (hm : y 0 < 1)
    (hd : exitClockRate y ≠ 0) (n : ℕ) :
    ContDiffAt ℝ n (fun p : ℝ × ExitTailState => exitTailField (Real.exp (-p.1)) p.2)
      (exitLogClock y, toExitTailState y) := by
  have hrad := coreRadius_pos (m := y 0) hV
  have hvR : (y 2) ^ 2 < coreRadius (y 0) (y 2) ^ 2 := by
    rw [coreRadius_sq]
    dsimp only [coreEnergy]
    nlinarith only [sq_pos_of_neg (sub_neg.mpr hm)]
  have hspeed : exitTailSpeed (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) ≠ 0 := by
    rwa [← exitClockRate_tail hm]
  have HF := contDiffAt_exitTailField n (v := y 2) (Y := toExitTailState y) hvR hrad.ne' hspeed
  have H : ContDiffAt ℝ n (fun p : ℝ × ExitTailState => exitTailField p.1 p.2)
      (Real.exp (-exitLogClock y), toExitTailState y) := by
    simpa only [exp_neg_exitLogClock hV] using HF
  have hmap : ContDiffAt ℝ n (fun p : ℝ × ExitTailState => (Real.exp (-p.1), p.2))
      (exitLogClock y, toExitTailState y) := by fun_prop
  exact H.comp (exitLogClock y, toExitTailState y) hmap

/-- The derivative of the actual joint clock family satisfies the first variational equation. -/
theorem hasDerivAt_exitClockFlow_variation {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {t : ℝ} (ht : t ∈ I)
    (v : ExitTailState) :
    HasDerivAt (fun s => fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))
      (fderiv ℝ (exitTailField (Real.exp (-exitEntryClock (Y, t))))
        (exitClockFlow I (Y, exitEntryClock (Y, t)))
        (fderiv ℝ (exitClockFlow I) (Y, exitEntryClock (Y, t)) (v, 0)))
      (exitEntryClock (Y, t)) := by
  have HR := H Y hY t ht
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  have HF : DifferentiableAt ℝ (fun p : ℝ × ExitTailState => exitTailField (Real.exp (-p.1)) p.2)
      (exitEntryClock (Y, t), exitClockFlow I (Y, exitEntryClock (Y, t))) := by
    rw [exitClockFlow_eq hI (H Y hY) ht]
    exact (contDiffAt_exitClockField HR.2.2.2.2.1 HR.2.2.2.2.2.1 HR.2.2.2.2.2.2.ne' 1).differentiableAt
      (by norm_num)
  exact hasDerivAt_parametric_first_variation (contDiffAt_exitClockFlow_two hIo hI ht HY)
    HF (exitClockFlow_local_partial_time hIo hI hUo hY H ht) v

theorem exitClockFlow_variation_initial {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) (h0 : (0 : ℝ) ∈ I) (v : ExitTailState) :
    fderiv ℝ (exitClockFlow I) (Y, 0) (v, 0) = v := by
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  have HC := contDiffAt_exitClockFlow_two hIo hI h0 HY
  rw [exitEntryClock_initial (H Y hY 0 h0).2.1] at HC
  have HE : (fun Z => exitClockFlow I (Z, 0)) =ᶠ[𝓝 Y] id := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact exitClockFlow_initial hI (H Z hZ) h0
  have hslice : HasFDerivAt (fun Z : ExitTailState => (Z, (0 : ℝ)))
      ((ContinuousLinearMap.id ℝ ExitTailState).prod 0) Y :=
    (hasFDerivAt_id Y).prodMk (hasFDerivAt_const (0 : ℝ) Y)
  have HD := (HC.differentiableAt (by norm_num)).hasFDerivAt.comp Y hslice
  have HI := (HD.congr_of_eventuallyEq HE.symm).unique (hasFDerivAt_id Y)
  exact congrArg (fun L : ExitTailState →L[ℝ] ExitTailState => L v) HI

end BianchiIX
