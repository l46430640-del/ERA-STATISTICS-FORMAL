import BianchiIX.Dynamics.ExitClockVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem exitEntryClock_interval_surjective {Y : ExitTailState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc 0 T, exitEntryRegular Y t) {s : ℝ}
    (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) :
    ∃ t ∈ Icc 0 T, exitEntryClock (Y, t) = s := by
  have HC : ContinuousOn (fun t => exitEntryClock (Y, t)) (Icc 0 T) :=
    HasDerivAt.continuousOn (fun t ht => hasDerivAt_exitEntryClock (H t ht))
  have H0 := exitEntryClock_initial (H 0 ⟨le_rfl, hT⟩).2.1
  exact intermediate_value_Icc hT HC (by rwa [H0])

/-- The actual clock flow is regular and solves its ODE at every clock value of the flight. -/
theorem exitClockFlow_on_interval {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) {s : ℝ} (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) :
    ContDiffAt ℝ 2 (exitClockFlow I) (Y, s) ∧
      HasDerivAt (fun r => exitClockFlow I (Y, r))
        (exitTailField (Real.exp (-s)) (exitClockFlow I (Y, s))) s ∧
      ∀ v : ExitTailState,
        HasDerivAt (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0))
          (fderiv ℝ (exitTailField (Real.exp (-s))) (exitClockFlow I (Y, s))
            (fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))) s := by
  obtain ⟨t, ht, he⟩ := exitEntryClock_interval_surjective hT (fun r hr => H Y hY r (hcover hr)) hs
  have HL := (exitClockFlow_local_ode hIo hI hUo hY H (hcover ht)).self_of_nhds
  have HV := hasDerivAt_exitClockFlow_variation hIo hI hUo hY H (hcover ht)
  rw [he] at HL HV
  exact ⟨HL.1, HL.2, HV⟩

theorem coreTailState_eq_exitClockFlow {I : Set ℝ} (hI : Convex ℝ I) {Y : ExitTailState} {h : ℝ}
    (H : ∀ r ∈ I, exitEntryRegular Y r) (hvalid : coreTailValid h Y)
    (ht : coreTailTime h Y ∈ I) :
    toExitTailState (coreTailState h Y) = exitClockFlow I (Y, -Real.log h) := by
  have HE := exitClockFlow_eq hI H ht
  have HC : exitEntryClock (Y, coreTailTime h Y) = -Real.log h := by
    change -Real.log (coreTailState h Y 2) = -Real.log h
    rw [coreTailState_active hvalid]
  rw [HC] at HE
  exact HE.symm

/-- The smooth inverse branch agrees with the canonical arrival map on a neighborhood of the initial state. -/
theorem coreTailState_eventuallyEq_exitClockFlow {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {h : ℝ}
    (hvalid : coreTailValid h Y) (ht : coreTailTime h Y ∈ I) :
    (fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y]
      (fun Z => exitClockFlow I (Z, -Real.log h)) := by
  obtain ⟨hτ, _, hnear⟩ := coreTail_regular_of_valid (H Y hY _ ht).1 hvalid
  filter_upwards [hnear, hUo.mem_nhds hY, hτ.continuousAt.eventually (hIo.mem_nhds ht)] with Z hZ hZU hZI
  exact coreTailState_eq_exitClockFlow hI (H Z hZU) hZ hZI

end BianchiIX
