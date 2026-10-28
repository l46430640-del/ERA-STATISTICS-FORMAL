import BianchiIX.Dynamics.DownwardReturnRestart
import BianchiIX.Dynamics.ShearRestartEntranceReturn
import BianchiIX.Dynamics.ShearRestartReturnRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Two fixed nonnegative cutoffs describe the same flow in a full neighborhood of the input labels. -/
theorem restartFastShearProjectiveEntry_shift_eventuallyEq {h s S σ n₂ n₃ ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ))
    (hs : 0 ≤ s) (hS : 0 ≤ S) (hA : 0 < restartFastShearHeight h s σ n₂ n₃ ρ) :
    (fun v : (ℝ × ℝ) × ℝ => projectiveOriginalFlow
      (restartFastShearProjectiveEntry h s σ v.1.1 v.1.2 v.2) 0 S) =ᶠ[𝓝 ((n₂, n₃), ρ)]
      (fun v => restartFastShearProjectiveEntry h (S + s) σ v.1.1 v.1.2 v.2) := by
  let base : (ℝ × ℝ) × ℝ := ((n₂, n₃), ρ)
  have hcurve : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearCurve σ v.1.1 v.1.2 v.2) base := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [restartShearCurve] <;> fun_prop
  have hc : ContinuousAt (fun v : (ℝ × ℝ) × ℝ =>
      restartSectionRadicand h (restartShearCurve σ v.1.1 v.1.2 v.2)) base := by
    dsimp [restartSectionRadicand, restartShearCurve, curvature]
    fun_prop
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hs
  have hchart := (contDiffAt_restartSectionChart hrad 2).comp base hcurve
  have hflow := (contDiffAt_normalizedMaxCurve_two hdom).comp base
    (g := fun v : NormalizedState × ℝ => normalizedMaxCurve v.1 0 v.2)
    (hchart.prodMk (contDiffAt_const (c := s)))
  have hheight : ContinuousAt (fun v : (ℝ × ℝ) × ℝ => restartFastShearHeight h s σ v.1.1 v.1.2 v.2) base :=
    continuousAt_const.add (continuousAt_pi.mp hflow.continuousAt 0)
  filter_upwards [hc.eventually (lt_mem_nhds hrad), hheight.eventually (lt_mem_nhds hA)] with v hv hAv
  simpa only [restartFastShearProjectiveEntry, add_comm s S] using
    restartFastShearProjectiveEntry_flow hv.le hs hAv hS

/-- A strict below-section prefix changes neither the return nor its ordinary germ, including total time. -/
theorem restartShearReturn_cutoff_eventuallyEq {h s S n₂ n₃ ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ))
    (hs : 0 ≤ s) (hS : 0 ≤ S)
    (hprefix : ∀ t ∈ Icc 0 S,
      0 < restartFastShearHeight h (t + s) 1 n₂ n₃ ρ ∧
        restartFastShearProjectiveEntry h (t + s) 1 n₂ n₃ ρ 2 < 1)
    (Hnear : ∀ᶠ z in 𝓝 (restartFastShearProjectiveEntry h (S + s) 1 n₂ n₃ ρ),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreDownwardReturnTime z)) :
    (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((n₂, n₃), ρ)]
      (fun v => restartShearReturnParameters h (S + s) v.1.1 v.1.2 v.2) ∧
    (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((n₂, n₃), ρ)]
      (fun v => restartShearReturnState h (S + s) v.1.1 v.1.2 v.2) ∧
    (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((n₂, n₃), ρ)]
      (fun v => restartShearReturnPhase h (S + s) v.1.1 v.1.2 v.2) ∧
    (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((n₂, n₃), ρ)]
      (fun v => restartShearReturnTime h (S + s) v.1.1 v.1.2 v.2) := by
  let base : (ℝ × ℝ) × ℝ := ((n₂, n₃), ρ)
  let Y := fun v : (ℝ × ℝ) × ℝ => restartFastShearProjectiveEntry h s 1 v.1.1 v.1.2 v.2
  have hA : 0 < restartFastShearHeight h s 1 n₂ n₃ ρ := by
    simpa only [zero_add] using (hprefix 0 ⟨le_rfl, hS⟩).1
  have hc := restartSectionChart_constraint hrad.le
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hD : 0 < projectiveStateDenom (Y base) :=
    toProjectiveState_denom_pos hA ((normalizedMaxCurve_constraint hdom).trans hc)
  have hreg : ∀ t ∈ Icc 0 S, t ∈ normalizedMaxDomain (fromProjectiveState (Y base)) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState (Y base)) 0 t 0 ∧
      projectiveOriginalFlow (Y base) 0 t 2 < 1 := by
    intro t ht
    refine ⟨normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hD.ne') 0 ht.1, ?_, ?_⟩
    · rw [restartFastShearProjectiveEntry_normalized_flow hrad.le hs hA ht.1, add_comm s t]
      exact (hprefix t ht).1
    · rw [restartFastShearProjectiveEntry_flow hrad.le hs hA ht.1, add_comm s t]
      exact (hprefix t ht).2
  have Hshift := restartFastShearProjectiveEntry_shift_eventuallyEq hrad hs hS hA
  have Hnear' : ∀ᶠ z in 𝓝 (projectiveOriginalFlow (Y base) 0 S),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreDownwardReturnTime z) := by
    have Heq : projectiveOriginalFlow (Y base) 0 S = restartFastShearProjectiveEntry h (S + s) 1 n₂ n₃ ρ :=
      Hshift.self_of_nhds
    rw [Heq]
    exact Hnear
  have HR := partialCoreDownwardReturn_restart_eventuallyEq hD hS hreg Hnear'
  have hcY : ContinuousAt Y base :=
    (contDiffAt_restartFastShearProjectiveEntry_joint hrad hdom hA.ne').continuousAt
  have H : ∀ᶠ v in 𝓝 base,
      restartShearReturnParameters h s v.1.1 v.1.2 v.2 = restartShearReturnParameters h (S + s) v.1.1 v.1.2 v.2 ∧
      restartShearReturnState h s v.1.1 v.1.2 v.2 = restartShearReturnState h (S + s) v.1.1 v.1.2 v.2 ∧
      restartShearReturnPhase h s v.1.1 v.1.2 v.2 = restartShearReturnPhase h (S + s) v.1.1 v.1.2 v.2 ∧
      restartShearReturnTime h s v.1.1 v.1.2 v.2 = restartShearReturnTime h (S + s) v.1.1 v.1.2 v.2 := by
    filter_upwards [Hshift, hcY.tendsto.eventually HR.1, hcY.tendsto.eventually HR.2] with v hv ht hz
    change partialCoreDownwardReturnTime (Y v) = S + partialCoreDownwardReturnTime (projectiveOriginalFlow (Y v) 0 S) at ht
    change partialCoreDownwardReturnState (Y v) = partialCoreDownwardReturnState (projectiveOriginalFlow (Y v) 0 S) at hz
    rw [hv] at ht hz
    have hp : restartShearReturnParameters h s v.1.1 v.1.2 v.2 =
        restartShearReturnParameters h (S + s) v.1.1 v.1.2 v.2 := congrArg coreExitConnectionParameters hz
    have hg : restartShearReturnState h s v.1.1 v.1.2 v.2 =
        restartShearReturnState h (S + s) v.1.1 v.1.2 v.2 := congrArg connectionReturnPhysicalState hp
    refine ⟨hp, hg, congrArg (fun G : CoreAngleState => 2 / G 0) hg, ?_⟩
    dsimp only [restartShearReturnTime]
    change s + partialCoreDownwardReturnTime (Y v) + _ = _
    rw [ht, hp]
    ring
  exact ⟨H.mono fun _ h => h.1, H.mono fun _ h => h.2.1,
    H.mono fun _ h => h.2.2.1, H.mono fun _ h => h.2.2.2⟩

end BianchiIX
