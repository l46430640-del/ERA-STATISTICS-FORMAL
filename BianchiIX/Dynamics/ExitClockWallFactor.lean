import BianchiIX.Dynamics.ExitClockLogMultiplier

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem contDiffAt_exitClockRateIntegrand_graph {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {Y : ExitTailState} {t : ℝ} (ht : t ∈ I)
    (H : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r) (i : Fin 2) :
    ContDiffAt ℝ 1 (exitClockRateIntegrand I i) (Y, exitEntryClock (Y, t)) := by
  have HR := H.self_of_nhds t ht
  have he := exitClockFlow_eq hI H.self_of_nhds ht
  have hv : (Real.exp (-exitEntryClock (Y, t))) ^ 2 <
      (exitClockFlow I (Y, exitEntryClock (Y, t)) 0) ^ 2 := by
    rw [he]
    change (Real.exp (-exitLogClock (exitEntryFlow (Y, t)))) ^ 2 <
      coreRadius (exitEntryFlow (Y, t) 0) (exitEntryFlow (Y, t) 2) ^ 2
    rw [exp_neg_exitLogClock HR.2.2.2.2.1, coreRadius_sq]
    dsimp only [coreEnergy]
    nlinarith only [sq_pos_of_neg (sub_neg.mpr HR.2.2.2.2.2.1)]
  have hd : exitTailSpeed (exitClockFlow I (Y, exitEntryClock (Y, t)) 0)
      (exitClockFlow I (Y, exitEntryClock (Y, t)) 1) (Real.exp (-exitEntryClock (Y, t)))
      (exitClockFlow I (Y, exitEntryClock (Y, t)) 2) ≠ 0 := by
    rw [he]
    change exitTailSpeed (coreRadius (exitEntryFlow (Y, t) 0) (exitEntryFlow (Y, t) 2))
      (exitEntryFlow (Y, t) 1) (Real.exp (-exitLogClock (exitEntryFlow (Y, t)))) (exitEntryFlow (Y, t) 3) ≠ 0
    rw [exp_neg_exitLogClock HR.2.2.2.2.1, ← exitClockRate_tail HR.2.2.2.2.2.1]
    exact HR.2.2.2.2.2.2.ne'
  exact contDiffAt_exitClockRateIntegrand
    ((contDiffAt_exitClockFlow_two hIo hI ht H).of_le (by norm_num)) hv hd i

theorem exitClockFlow_near_wall_equation {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T s : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) (i : Fin 2) :
    ∀ᶠ Z in 𝓝 Y, ∀ r ∈ Icc 0 s,
      ContDiffAt ℝ 1 (exitClockRateIntegrand I i) (Z, r) ∧
      HasDerivAt (fun a => exitClockFlow I (Z, a))
        (exitTailField (Real.exp (-r)) (exitClockFlow I (Z, r))) r := by
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro r hr
  obtain ⟨t, ht, he⟩ := exitEntryClock_interval_surjective hT
    (fun t ht => H Y hY t (hcover ht)) ⟨hr.1, hr.2.trans hs.2⟩
  have HA := (contDiffAt_exitClockRateIntegrand_graph hIo hI (hcover ht) HY i).eventually (by norm_num)
  have HF := exitClockFlow_local_ode hIo hI hUo hY H (hcover ht)
  rw [he] at HA HF
  filter_upwards [HA, HF] with p hp hpf
  exact ⟨hp, hpf.2⟩

/-- The wall factorization holds on an initial-state neighborhood, including zero walls. -/
theorem exitClockFlow_eventually_wall_factor {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T s : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) (i : Fin 2) :
    (fun Z => exitClockFlow I (Z, s) i.succ) =ᶠ[𝓝 Y]
      (fun Z => Z i.succ * Real.exp (exitClockLogMultiplier I i Z s)) := by
  filter_upwards [exitClockFlow_near_wall_equation hIo hI hUo hY H hT hcover hs i,
    hUo.mem_nhds hY] with Z hZ hZU
  have hrate : ContinuousOn (fun r => exitClockRateIntegrand I i (Z, r)) (Icc 0 s) :=
    fun r hr => ((hZ r hr).1.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hwall (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt (fun a => exitClockFlow I (Z, a) i.succ)
      (exitClockRateIntegrand I i (Z, r) * exitClockFlow I (Z, r) i.succ) r := by
    have HD := hasDerivAt_pi.mp (hZ r hr).2 i.succ
    rwa [exitTailField_wall] at HD
  have HF := homogeneous_solution_eq_exp_integral_Icc hs.1 hrate (HasDerivAt.continuousOn hwall)
    (fun r hr => hwall r (Ioo_subset_Icc_self hr))
  rw [exitClockFlow_initial hI (H Z hZU) (hcover ⟨le_rfl, hT⟩)] at HF
  exact HF

theorem exitClockFlow_wall_differential {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T s : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) (i : Fin 2) (v : ExitTailState) :
    fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y v i.succ =
      Real.exp (exitClockLogMultiplier I i Y s) * v i.succ +
        exitClockFlow I (Y, s) i.succ * fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y v := by
  have Hnear := exitClockFlow_near_wall_equation hIo hI hUo hY H hT hcover hs i
  have hL := (exitClockLogMultiplier_regular hs.1 i (fun r hr => (Hnear.self_of_nhds r hr).1)).1
  have hΦ := (exitClockFlow_on_interval hIo hI hUo hY H hT hcover hs).1
  have hslice := hΦ.comp Y (contDiffAt_id.prodMk (contDiffAt_const (c := s)))
  have HS := hasFDerivAt_pi'.mp (hslice.differentiableAt (by norm_num)).hasFDerivAt i.succ
  have HE := exitClockFlow_eventually_wall_factor hIo hI hUo hY H hT hcover hs i
  have HD := (hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).mul
    ((hL.differentiableAt (by norm_num)).hasFDerivAt.exp)
  have HV := congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v)
    ((HS.congr_of_eventuallyEq HE.symm).unique HD)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, add_apply,
    smul_apply, smul_eq_mul, Function.comp_def, id_eq] at HV
  have Hval : exitClockFlow I (Y, s) i.succ = Y i.succ * Real.exp (exitClockLogMultiplier I i Y s) :=
    HE.self_of_nhds
  rw [Hval]
  nlinarith only [HV]

end BianchiIX
