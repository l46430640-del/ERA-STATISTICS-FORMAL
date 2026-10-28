import BianchiIX.Dynamics.PartialCoreReturnOrientation
import BianchiIX.Dynamics.DownwardReturnMovingCutoff
import BianchiIX.Dynamics.RestartReturnRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The exact angular cutoff preserves the normalized flow as well as its projective state. -/
theorem restartFastProjectiveEntry_normalized_flow {h s θ ζ ρ t : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastProjectionHeight h s θ ζ ρ) (ht : 0 ≤ t) :
    normalizedMaxCurve (fromProjectiveState (restartFastProjectiveEntry h s θ ζ ρ)) 0 t =
      normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 (s + t) := by
  have hc := restartSectionChart_constraint hrad
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hbase := fromProjectiveState_toProjectiveState hA.ne'
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))
  simp only [zero_add] at H
  change normalizedMaxCurve (fromProjectiveState (toProjectiveState
    (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 s))) 0 t = _
  rw [hbase, H, add_comm t s]

/-- A fixed shift of the angular cutoff holds on a full ordinary neighborhood of the labels. -/
theorem restartFastProjectiveEntry_shift_eventuallyEq {h s S θ ζ ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : 0 ≤ s) (hS : 0 ≤ S) (hA : 0 < restartFastProjectionHeight h s θ ζ ρ) :
    (fun v : (ℝ × ℝ) × ℝ => projectiveOriginalFlow
      (restartFastProjectiveEntry h s v.1.1 v.1.2 v.2) 0 S) =ᶠ[𝓝 ((θ, ζ), ρ)]
      (fun v => restartFastProjectiveEntry h (S + s) v.1.1 v.1.2 v.2) := by
  let base : (ℝ × ℝ) × ℝ := ((θ, ζ), ρ)
  have hcurve : ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartRadialCurve v.1.1 v.1.2 v.2) base := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [restartRadialCurve] <;> fun_prop
  have hc : ContinuousAt (fun v : (ℝ × ℝ) × ℝ =>
      restartSectionRadicand h (restartRadialCurve v.1.1 v.1.2 v.2)) base := by
    dsimp [restartSectionRadicand, restartRadialCurve, curvature]
    fun_prop
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hs
  have hchart := (contDiffAt_restartSectionChart hrad 2).comp base hcurve
  have hflow := (contDiffAt_normalizedMaxCurve_two hdom).comp base
    (g := fun v : NormalizedState × ℝ => normalizedMaxCurve v.1 0 v.2)
    (hchart.prodMk (contDiffAt_const (c := s)))
  have hheight : ContinuousAt (fun v : (ℝ × ℝ) × ℝ => restartFastProjectionHeight h s v.1.1 v.1.2 v.2) base :=
    continuousAt_const.add (continuousAt_pi.mp hflow.continuousAt 0)
  filter_upwards [hc.eventually (lt_mem_nhds hrad), hheight.eventually (lt_mem_nhds hA)] with v hv hAv
  simpa only [restartFastProjectiveEntry, add_comm s S] using restartFastProjectiveEntry_flow hv.le hs hAv hS

/-- A prefix above the section identifies all angular return germs, including total elapsed time. -/
theorem restartReturn_cutoff_eventuallyEq {h s S θ ζ ρ k₀ k₁ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : 0 ≤ s) (hS : 0 < S)
    (hprefix : ∀ t ∈ Icc 0 S,
      0 < restartFastProjectionHeight h (t + s) θ ζ ρ ∧
        1 < restartFastProjectiveEntry h (t + s) θ ζ ρ 2)
    (hk₀ : 6 ≤ k₀) (hy₀ : coreRegion k₀ (restartFastProjectiveEntry h s θ ζ ρ))
    (hR₀ : coreRadius (restartFastProjectiveEntry h s θ ζ ρ 0)
      (restartFastProjectiveEntry h s θ ζ ρ 2) = k₀)
    (hk₁ : 6 ≤ k₁) (hy₁ : coreRegion k₁ (restartFastProjectiveEntry h (S + s) θ ζ ρ))
    (hR₁ : coreRadius (restartFastProjectiveEntry h (S + s) θ ζ ρ 0)
      (restartFastProjectiveEntry h (S + s) θ ζ ρ 2) = k₁) :
    (fun v : (ℝ × ℝ) × ℝ => restartReturnParameters h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((θ, ζ), ρ)]
      (fun v => restartReturnParameters h (S + s) v.1.1 v.1.2 v.2) ∧
    (fun v : (ℝ × ℝ) × ℝ => restartReturnState h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((θ, ζ), ρ)]
      (fun v => restartReturnState h (S + s) v.1.1 v.1.2 v.2) ∧
    (fun v : (ℝ × ℝ) × ℝ => restartReturnPhase h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((θ, ζ), ρ)]
      (fun v => restartReturnPhase h (S + s) v.1.1 v.1.2 v.2) ∧
    (fun v : (ℝ × ℝ) × ℝ => restartReturnTime h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((θ, ζ), ρ)]
      (fun v => restartReturnTime h (S + s) v.1.1 v.1.2 v.2) := by
  let base : (ℝ × ℝ) × ℝ := ((θ, ζ), ρ)
  let Y₀ := fun v : (ℝ × ℝ) × ℝ => restartFastProjectiveEntry h s v.1.1 v.1.2 v.2
  let Y₁ := fun v : (ℝ × ℝ) × ℝ => restartFastProjectiveEntry h (S + s) v.1.1 v.1.2 v.2
  have H₀ : 0 < restartFastProjectionHeight h s θ ζ ρ ∧ 1 < Y₀ base 2 := by
    simpa only [zero_add] using hprefix 0 ⟨le_rfl, hS.le⟩
  have H₁ := hprefix S ⟨hS.le, le_rfl⟩
  have hc := restartSectionChart_constraint hrad.le
  have hdom₀ := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hdom₁ := normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg hS.le hs)
  have hD : 0 < projectiveStateDenom (Y₀ base) :=
    toProjectiveState_denom_pos H₀.1 ((normalizedMaxCurve_constraint hdom₀).trans hc)
  have hreg : ∀ t ∈ Icc 0 S, t ∈ normalizedMaxDomain (fromProjectiveState (Y₀ base)) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState (Y₀ base)) 0 t 0 := by
    intro t ht
    refine ⟨normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hD.ne') 0 ht.1, ?_⟩
    rw [restartFastProjectiveEntry_normalized_flow hrad.le hs H₀.1 ht.1, add_comm s t]
    exact (hprefix t ht).1
  have hbefore : ∀ t ∈ Icc 0 S, projectiveOriginalFlow (Y₀ base) 0 t 2 ≠ 1 ∨
      0 < normalizedEventRate projectiveActiveWall (fromProjectiveState (Y₀ base)) 0 t := by
    intro t ht
    left
    have HF := restartFastProjectiveEntry_flow hrad.le hs H₀.1 ht.1
    change projectiveOriginalFlow (Y₀ base) 0 t = _ at HF
    rw [HF, add_comm s t]
    exact ne_of_gt (hprefix t ht).2
  have Hshift := restartFastProjectiveEntry_shift_eventuallyEq hrad hs hS.le H₀.1
  have Hend : projectiveOriginalFlow (Y₀ base) 0 S = Y₁ base := Hshift.self_of_nhds
  have Hnear := (partialCoreDownwardReturn_regular hk₁ hy₁ hR₁ (Or.inl H₁.2)).2.2.2.1.mono fun _ H => H.1
  have HR := partialCoreDownwardReturn_moving_cutoff_eventuallyEq (Θ := fun _ => S)
    hD continuousAt_const hS hreg hbefore (by rw [Hend]; exact Hnear)
  have HE₀ := partialCoreDownwardReturn_agrees_eventually hk₀ hy₀ hR₀ H₀.2
  have HE₁ := partialCoreDownwardReturn_agrees_eventually hk₁ hy₁ hR₁ H₁.2
  have hc₀ : ContinuousAt Y₀ base := (contDiffAt_restartFastProjectiveEntry_joint hrad hdom₀ H₀.1.ne').continuousAt
  have hc₁ : ContinuousAt Y₁ base := (contDiffAt_restartFastProjectiveEntry_joint hrad hdom₁ H₁.1.ne').continuousAt
  have H : ∀ᶠ v in 𝓝 base,
      restartReturnParameters h s v.1.1 v.1.2 v.2 = restartReturnParameters h (S + s) v.1.1 v.1.2 v.2 ∧
      restartReturnState h s v.1.1 v.1.2 v.2 = restartReturnState h (S + s) v.1.1 v.1.2 v.2 ∧
      restartReturnPhase h s v.1.1 v.1.2 v.2 = restartReturnPhase h (S + s) v.1.1 v.1.2 v.2 ∧
      restartReturnTime h s v.1.1 v.1.2 v.2 = restartReturnTime h (S + s) v.1.1 v.1.2 v.2 := by
    filter_upwards [Hshift, hc₀.tendsto.eventually HR.1, hc₀.tendsto.eventually HR.2,
      hc₀.tendsto.eventually HE₀.1, hc₀.tendsto.eventually HE₀.2,
      hc₁.tendsto.eventually HE₁.1, hc₁.tendsto.eventually HE₁.2] with v hv ht hz ht₀ hz₀ ht₁ hz₁
    change partialCoreDownwardReturnTime (Y₀ v) = S + partialCoreDownwardReturnTime (projectiveOriginalFlow (Y₀ v) 0 S) at ht
    change partialCoreDownwardReturnState (Y₀ v) = partialCoreDownwardReturnState (projectiveOriginalFlow (Y₀ v) 0 S) at hz
    rw [hv, ht₀, ht₁] at ht
    rw [hv, hz₀, hz₁] at hz
    have hp : restartReturnParameters h s v.1.1 v.1.2 v.2 =
        restartReturnParameters h (S + s) v.1.1 v.1.2 v.2 := congrArg coreExitConnectionParameters hz
    have hg : restartReturnState h s v.1.1 v.1.2 v.2 =
        restartReturnState h (S + s) v.1.1 v.1.2 v.2 := congrArg connectionReturnPhysicalState hp
    refine ⟨hp, hg, congrArg (fun G : CoreAngleState => 2 / G 0) hg, ?_⟩
    dsimp only [restartReturnTime]
    change s + partialCoreReturnTime (Y₀ v) + _ = _
    rw [ht, hp]
    ring
  exact ⟨H.mono fun _ h => h.1, H.mono fun _ h => h.2.1,
    H.mono fun _ h => h.2.2.1, H.mono fun _ h => h.2.2.2⟩

end BianchiIX
