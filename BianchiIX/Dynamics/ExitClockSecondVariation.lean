import BianchiIX.Dynamics.ExitClockSecondSource
import BianchiIX.Analysis.ParametricVariationIntegral

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem exitClockFlow_graph_regular {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {Y : ExitTailState} {t : ℝ} (ht : t ∈ I)
    (H : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r) :
    ContDiffAt ℝ 2 (exitClockFlow I) (Y, exitEntryClock (Y, t)) ∧
      ContDiffAt ℝ 1 (fun p : ℝ × ExitTailState => fderiv ℝ (exitTailField (Real.exp (-p.1))) p.2)
        (exitEntryClock (Y, t), exitClockFlow I (Y, exitEntryClock (Y, t))) := by
  have HR := H.self_of_nhds t ht
  refine ⟨contDiffAt_exitClockFlow_two hIo hI ht H, ?_⟩
  rw [exitClockFlow_eq hI H.self_of_nhds ht]
  exact contDiffAt_exitClock_stateDerivative HR.2.2.2.2.1 HR.2.2.2.2.2.1 HR.2.2.2.2.2.2.ne'

theorem exitClockFlow_local_variation {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {t : ℝ} (ht : t ∈ I) (w : ExitTailState) :
    ∀ᶠ p in 𝓝 (Y, exitEntryClock (Y, t)),
      ContDiffAt ℝ 1 (exitClockVariationRate I w) p ∧
      HasDerivAt (fun s => fderiv ℝ (exitClockFlow I) (p.1, s) (w, 0))
        (exitClockVariationRate I w p) p.2 := by
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  have Hp := (show ContinuousAt (fun p : ExitTailState × ℝ => p.1)
    (Y, exitEntryClock (Y, t)) from continuousAt_fst).eventually (hUo.mem_nhds hY)
  filter_upwards [(exitClockTime_regular hIo hI ht HY).2, Hp] with p hp hpu
  have HZ : ∀ᶠ Z in 𝓝 p.1, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hpu] with Z hZ
    exact H Z hZ
  have HR := exitClockFlow_graph_regular hIo hI hp.1 HZ
  have HD := hasDerivAt_exitClockFlow_variation hIo hI hUo hpu H hp.1 w
  rw [hp.2] at HR HD
  exact ⟨contDiffAt_exitClockVariationRate_one HR.1 HR.2 w, HD⟩

/-- The ordinary Hessian of the actual clock map is represented by the forced variational system. -/
theorem exists_exitClockFlow_second_variation {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (v w : ExitTailState) :
    ∃ Q : ℝ → ExitTailState, Q 0 = 0 ∧ ∀ s ∈ Icc 0 (exitEntryClock (Y, T)),
      Q s = fderiv ℝ (fderiv ℝ (fun Z => exitClockFlow I (Z, s))) Y v w ∧
      HasDerivAt Q
        (fderiv ℝ (exitTailField (Real.exp (-s))) (exitClockFlow I (Y, s)) (Q s) +
          fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (exitClockFlow I (Y, s))
            (fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))
            (fderiv ℝ (exitClockFlow I) (Y, s) (w, 0))) s := by
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  have Hpre {s : ℝ} (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) :
      ∃ t ∈ Icc 0 T, exitEntryClock (Y, t) = s :=
    exitEntryClock_interval_surjective hT (fun t ht => H Y hY t (hcover ht)) hs
  have HG (s : ℝ) (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) :
      ContDiffAt ℝ 1 (exitClockVariationRate I w) (Y, s) := by
    obtain ⟨t, ht, he⟩ := Hpre hs
    simpa only [he] using (exitClockFlow_local_variation hIo hI hUo hY H (hcover ht) w).self_of_nhds.1
  have HJ : ∀ᶠ Z in 𝓝 Y, ∀ s ∈ Icc 0 (exitEntryClock (Y, T)),
      HasDerivAt (fun r => fderiv ℝ (exitClockFlow I) (Z, r) (w, 0))
        (exitClockVariationRate I w (Z, s)) s := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    obtain ⟨t, ht, he⟩ := Hpre hs
    have HL := (exitClockFlow_local_variation hIo hI hUo hY H (hcover ht) w).mono fun _ h => h.2
    simpa only [he] using HL
  have hi : ∀ᶠ Z in 𝓝 Y, fderiv ℝ (exitClockFlow I) (Z, 0) (w, 0) = w := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact exitClockFlow_variation_initial hIo hI hUo hZ H (hcover ⟨le_rfl, hT⟩) w
  obtain ⟨Q, hQ0, HQ⟩ := exists_parametric_variation_integral
    (J := fun p : ExitTailState × ℝ => fderiv ℝ (exitClockFlow I) p (w, 0))
    (G := exitClockVariationRate I w) HG HJ hi v
  refine ⟨Q, hQ0, ?_⟩
  intro s hs
  obtain ⟨t, ht, he⟩ := Hpre hs
  have HR := exitClockFlow_graph_regular hIo hI (hcover ht) HY
  rw [he] at HR
  refine ⟨(HQ s hs).1.trans (fderiv_parameterVariation_apply HR.1 v w), ?_⟩
  have HD := (HQ s hs).2
  rwa [exitClockVariationRate_fderiv_initial HR.1 HR.2 v w, ← (HQ s hs).1] at HD

end BianchiIX
