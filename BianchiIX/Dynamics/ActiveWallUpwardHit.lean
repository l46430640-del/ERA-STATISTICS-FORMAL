import BianchiIX.Dynamics.ActiveWallFirstHit

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem eventually_activeWall_first_upward_hit {x : NormalizedState} {τ : NormalizedState → ℝ} {η : ℝ}
    (hcτ : ContinuousAt τ x) (hT : 0 < τ x)
    (hreg : ∀ t ∈ Icc 0 (τ x), t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0)
    (hrate : ∀ t ∈ Icc 0 (τ x), 0 < normalizedEventRate projectiveActiveWall x 0 t)
    (hhit : ∀ᶠ y in 𝓝 x, projectiveActiveWall (normalizedMaxCurve y 0 (τ y)) = η) :
    ∀ᶠ y in 𝓝 x,
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain y 0 ∧ projectiveActiveWall (normalizedMaxCurve y 0 t) = η} (τ y) ∧
      (∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0) ∧
      (∀ t ∈ Ico 0 (τ y), projectiveActiveWall (normalizedMaxCurve y 0 t) < η) ∧
      (∀ t ∈ Icc 0 (τ y), 0 < normalizedEventRate projectiveActiveWall y 0 t) := by
  have hpersist : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc 0 (τ y),
      t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0 ∧
        0 < normalizedEventRate projectiveActiveWall y 0 t := by
    apply eventually_forall_movingInterval hcτ hT
    intro t ht
    have hflow := (normalizedMaxCurve_regular (hreg t ht).1).2.continuousAt
    have hA : ContinuousAt (fun z : NormalizedState × ℝ => 1 + normalizedMaxCurve z.1 0 z.2 0) (x, t) :=
      continuousAt_const.add (continuousAt_pi.mp hflow 0)
    have hdom : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 0 :=
      (isOpen_normalizedFlowDomain 0).mem_nhds (hreg t ht).1
    exact hdom.and
      ((hA.eventually (isOpen_Ioi.mem_nhds (hreg t ht).2)).and
        ((continuousAt_activeWall_event_rate (hreg t ht).1 (hreg t ht).2.ne').eventually
          (isOpen_Ioi.mem_nhds (hrate t ht))))
  have hpos := hcτ.eventually (isOpen_Ioi.mem_nhds hT)
  filter_upwards [hpersist, hpos, hhit] with y hy hτ hhit_y
  have htmem : τ y ∈ Icc 0 (τ y) := ⟨hτ.le, le_rfl⟩
  have hd (t : ℝ) (ht : t ∈ Icc 0 (τ y)) :
      HasDerivAt (fun s => projectiveActiveWall (normalizedMaxCurve y 0 s))
        (normalizedEventRate projectiveActiveWall y 0 t) t := by
    exact ((contDiffAt_projectiveActiveWall 1 (hy t ht).2.1.ne').differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve (hy t ht).1)
  have hmono : StrictMonoOn (fun t => projectiveActiveWall (normalizedMaxCurve y 0 t)) (Icc 0 (τ y)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (HasDerivAt.continuousOn hd)
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact (hy t (interior_subset ht)).2.2
  have hbefore (t : ℝ) (ht : t ∈ Ico 0 (τ y)) : projectiveActiveWall (normalizedMaxCurve y 0 t) < η := by
    simpa only [hhit_y] using hmono ⟨ht.1, ht.2.le⟩ htmem ht.2
  refine ⟨⟨⟨hτ, (hy _ htmem).1, hhit_y⟩, ?_⟩,
    (fun t ht => ⟨(hy t ht).1, (hy t ht).2.1⟩), hbefore, fun t ht => (hy t ht).2.2⟩
  intro t ht
  by_contra hnot
  have H := hbefore t ⟨ht.1.le, lt_of_not_ge hnot⟩
  rw [ht.2.2] at H
  exact lt_irrefl _ H

theorem exists_activeWall_first_upward_hit_two {x : NormalizedState} {T η : ℝ} (hT : 0 < T)
    (hreg : ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0)
    (hrate : ∀ t ∈ Icc 0 T, 0 < normalizedEventRate projectiveActiveWall x 0 t)
    (hhit : projectiveActiveWall (normalizedMaxCurve x 0 T) = η) :
    ∃ τ : NormalizedState → ℝ, τ x = T ∧ ContDiffAt ℝ 2 τ x ∧
      ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y))) x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x 0 T) x ∧
      HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y)))
        ((fderiv ℝ toProjectiveState (normalizedMaxCurve x 0 T)).comp
          (normalizedEventDifferential projectiveActiveWall x 0 T)) x ∧
      (∀ᶠ y in 𝓝 x,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain y 0 ∧ projectiveActiveWall (normalizedMaxCurve y 0 t) = η} (τ y) ∧
        (∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0) ∧
        (∀ t ∈ Ico 0 (τ y), projectiveActiveWall (normalizedMaxCurve y 0 t) < η) ∧
        (∀ t ∈ Icc 0 (τ y), 0 < normalizedEventRate projectiveActiveWall y 0 t)) := by
  have htmem : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hdom := (hreg T htmem).1
  have hA := (hreg T htmem).2.ne'
  have hg := contDiffAt_projectiveActiveWall 2 hA
  obtain ⟨τ, hτ, hcτ, hdτ, hlocal, _, _, hdEnd⟩ := exists_normalized_event hdom
    (contDiffAt_projectiveActiveWall 1 hA) (hrate T htmem).ne'
  let F : NormalizedState × ℝ → NormalizedState := fun z => normalizedMaxCurve z.1 0 z.2
  let Q : NormalizedState × ℝ → ℝ := fun z => projectiveActiveWall (F z)
  have hcF : ContDiffAt ℝ 2 F (x, T) := contDiffAt_normalizedMaxCurve_two hdom
  have hcQ : ContDiffAt ℝ 2 Q (x, T) :=
    ContDiffAt.comp (g := projectiveActiveWall) (f := F) (x, T) hg hcF
  have htime : HasDerivAt (fun s => Q (x, s)) (normalizedEventRate projectiveActiveWall x 0 T) T :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt T (hasDerivAt_normalizedMaxCurve hdom)
  have hτ2 := contDiffAt_scalar_event_branch_two hcQ htime (hrate T htmem).ne' hτ
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
        (normalizedEventDifferential projectiveActiveWall x 0 T)) x := by
    apply HasFDerivAt.comp (g := toProjectiveState) (f := fun y => normalizedMaxCurve y 0 (τ y)) x _ hdEnd
    simpa only [hτ] using hdOut
  refine ⟨τ, hτ, hτ2, hcOut, hdτ, hdOut', ?_⟩
  apply eventually_activeWall_first_upward_hit hcτ.continuousAt
    (by rw [hτ]; exact hT) (by simpa only [hτ] using hreg) (by simpa only [hτ] using hrate)
  exact hlocal.mono fun _ h => h.2.trans hhit

end BianchiIX
