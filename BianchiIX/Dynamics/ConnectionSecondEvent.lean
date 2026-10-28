import BianchiIX.Dynamics.ConnectionEventPersistence
import BianchiIX.Dynamics.FlowSecondRegularity
import BianchiIX.Analysis.ImplicitBranch

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- A growing-wall flight gives an actual first-hit branch with two ambient derivatives. -/
theorem exists_growingWall_first_hit_two {x : NormalizedState} {T : ℝ} (hT : 0 < T)
    (hreg : ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0)
    (hrate : ∀ t ∈ Icc 0 T, 0 < normalizedEventRate projectiveGrowingWall x 0 t)
    (hhit : projectiveGrowingWall (normalizedMaxCurve x 0 T) = 1) :
    ∃ τ : NormalizedState → ℝ, τ x = T ∧ ContDiffAt ℝ 2 τ x ∧
      ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y))) x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential projectiveGrowingWall x 0 T) x ∧
      HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y)))
        ((fderiv ℝ toProjectiveState (normalizedMaxCurve x 0 T)).comp
          (normalizedEventDifferential projectiveGrowingWall x 0 T)) x ∧
      (∀ᶠ y in 𝓝 x,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain y 0 ∧ projectiveGrowingWall (normalizedMaxCurve y 0 t) = 1} (τ y) ∧
        (∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0) ∧
        (∀ t ∈ Ico 0 (τ y), projectiveGrowingWall (normalizedMaxCurve y 0 t) < 1) ∧
        0 < normalizedEventRate projectiveGrowingWall y 0 (τ y)) := by
  have htmem : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hdom := (hreg T htmem).1
  have hA := ne_of_gt (hreg T htmem).2
  have hg := contDiffAt_projectiveGrowingWall 2 hA
  obtain ⟨τ, hτ, hcτ, hdτ, hlocal, _, _, hdEnd⟩ := exists_normalized_event hdom
    (contDiffAt_projectiveGrowingWall 1 hA) (ne_of_gt (hrate T htmem))
  let F : NormalizedState × ℝ → NormalizedState := fun z => normalizedMaxCurve z.1 0 z.2
  let Q : NormalizedState × ℝ → ℝ := fun z => projectiveGrowingWall (F z)
  have hcF : ContDiffAt ℝ 2 F (x, T) := contDiffAt_normalizedMaxCurve_two hdom
  have hcQ : ContDiffAt ℝ 2 Q (x, T) :=
    ContDiffAt.comp (g := projectiveGrowingWall) (f := F) (x, T) hg hcF
  have htime : HasDerivAt (fun s => Q (x, s)) (normalizedEventRate projectiveGrowingWall x 0 T) T :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt T (hasDerivAt_normalizedMaxCurve hdom)
  have hτ2 := contDiffAt_scalar_event_branch_two hcQ htime (ne_of_gt (hrate T htmem)) hτ
    hcτ.continuousAt (hlocal.mono fun _ h => h.2)
  have hcEnd : ContDiffAt ℝ 2 (fun y => F (y, τ y)) x := by
    have H : ContDiffAt ℝ 2 F (x, τ x) := by rw [hτ]; exact hcF
    exact H.comp x (contDiffAt_id.prodMk hτ2)
  have hto : ContDiffAt ℝ 2 toProjectiveState (F (x, τ x)) := by
    rw [hτ]
    exact contDiffAt_toProjectiveState 2 hA
  have hcOut : ContDiffAt ℝ 2 (fun y => toProjectiveState (F (y, τ y))) x :=
    ContDiffAt.comp (g := toProjectiveState) (f := fun y => F (y, τ y)) x hto hcEnd
  have hdOut := ((contDiffAt_toProjectiveState 1 hA).differentiableAt (by norm_num)).hasFDerivAt
  have hdOut' : HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y)))
      ((fderiv ℝ toProjectiveState (normalizedMaxCurve x 0 T)).comp
        (normalizedEventDifferential projectiveGrowingWall x 0 T)) x := by
    apply HasFDerivAt.comp (g := toProjectiveState) (f := fun y => normalizedMaxCurve y 0 (τ y)) x _ hdEnd
    simpa only [hτ] using hdOut
  refine ⟨τ, hτ, hτ2, hcOut, hdτ, hdOut', ?_⟩
  apply eventually_growingWall_first_hit hcτ.continuousAt
    (by rw [hτ]; exact hT) (by simpa only [hτ] using hreg) (by simpa only [hτ] using hrate)
  exact hlocal.mono fun _ h => h.2.trans hhit

end BianchiIX
