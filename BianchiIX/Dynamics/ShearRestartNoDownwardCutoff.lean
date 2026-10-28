import BianchiIX.Dynamics.ShearRestartCutoffGerm
import BianchiIX.Dynamics.DownwardReturnMovingCutoff

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Allowing upward crossings between cutoffs preserves all complete return data on one ordinary label germ. -/
theorem restartShearReturn_no_downward_cutoff_eventuallyEq {h s S n₂ n₃ ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ))
    (hs : 0 ≤ s) (hS : 0 < S)
    (hprefix : ∀ t ∈ Icc 0 S,
      0 < restartFastShearHeight h (t + s) 1 n₂ n₃ ρ ∧
        (restartFastShearProjectiveEntry h (t + s) 1 n₂ n₃ ρ 2 ≠ 1 ∨
          0 < normalizedEventRate projectiveActiveWall
            (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 (t + s)))
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
    simpa only [zero_add] using (hprefix 0 ⟨le_rfl, hS.le⟩).1
  have hc := restartSectionChart_constraint hrad.le
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hD : 0 < projectiveStateDenom (Y base) :=
    toProjectiveState_denom_pos hA ((normalizedMaxCurve_constraint hdom).trans hc)
  have hreg : ∀ t ∈ Icc 0 S, t ∈ normalizedMaxDomain (fromProjectiveState (Y base)) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState (Y base)) 0 t 0 := by
    intro t ht
    refine ⟨normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hD.ne') 0 ht.1, ?_⟩
    rw [restartFastShearProjectiveEntry_normalized_flow hrad.le hs hA ht.1, add_comm s t]
    exact (hprefix t ht).1
  have hbefore : ∀ t ∈ Icc 0 S, projectiveOriginalFlow (Y base) 0 t 2 ≠ 1 ∨
      0 < normalizedEventRate projectiveActiveWall (fromProjectiveState (Y base)) 0 t := by
    intro t ht
    have HF := restartFastShearProjectiveEntry_flow hrad.le hs hA ht.1
    have HN := restartFastShearProjectiveEntry_normalized_flow hrad.le hs hA ht.1
    change projectiveOriginalFlow (Y base) 0 t = _ at HF
    change normalizedMaxCurve (fromProjectiveState (Y base)) 0 t = _ at HN
    rw [HF, normalizedEventRate, HN, add_comm s t]
    exact (hprefix t ht).2
  have Hshift := restartFastShearProjectiveEntry_shift_eventuallyEq hrad hs hS.le hA
  have Hnear' : ∀ᶠ z in 𝓝 (projectiveOriginalFlow (Y base) 0 S),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreDownwardReturnTime z) := by
    have Heq : projectiveOriginalFlow (Y base) 0 S =
        restartFastShearProjectiveEntry h (S + s) 1 n₂ n₃ ρ := Hshift.self_of_nhds
    rw [Heq]
    exact Hnear
  have HR := partialCoreDownwardReturn_moving_cutoff_eventuallyEq (Θ := fun _ => S)
    hD continuousAt_const hS hreg hbefore Hnear'
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
