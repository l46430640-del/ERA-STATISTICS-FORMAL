import BianchiIX.Dynamics.ActiveWallFirstHit

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Interior avoidance and local uniqueness at the terminal event preserve the first hit. -/
theorem eventually_activeWall_interior_first_hit {x : NormalizedState}
    {τ : NormalizedState → ℝ} {t₀ s η : ℝ}
    (hcτ : ContinuousAt τ x) (hst : s < τ x)
    (hreg : ∀ t ∈ Icc s (τ x), t ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (havoid : ∀ t ∈ Ico s (τ x), projectiveActiveWall (normalizedMaxCurve x t₀ t) ≠ η)
    (hhit : ∀ᶠ y in 𝓝 x, projectiveActiveWall (normalizedMaxCurve y t₀ (τ y)) = η)
    (huniq : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, τ x),
      projectiveActiveWall (normalizedMaxCurve z.1 t₀ z.2) = η → τ z.1 = z.2) :
    ∀ᶠ y in 𝓝 x,
      IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain y t₀ ∧
        projectiveActiveWall (normalizedMaxCurve y t₀ t) = η} (τ y) ∧
      (∀ t ∈ Icc s (τ y), t ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ t 0) := by
  have H : ∀ᶠ y in 𝓝 x, ∀ u ∈ Icc 0 (τ y - s),
      s + u ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ (s + u) 0 ∧
      (projectiveActiveWall (normalizedMaxCurve y t₀ (s + u)) = η → s + u = τ y) := by
    apply eventually_forall_movingInterval (hcτ.sub continuousAt_const) (sub_pos.mpr hst)
    intro u hu
    change u ∈ Icc 0 (τ x - s) at hu
    have hv : s + u ∈ Icc s (τ x) := ⟨by linarith only [hu.1], by linarith only [hu.2]⟩
    have hflow := (normalizedMaxCurve_regular (hreg _ hv).1).2.continuousAt
    have hAc : ContinuousAt (fun z : NormalizedState × ℝ => 1 + normalizedMaxCurve z.1 t₀ z.2 0) (x, s + u) :=
      continuousAt_const.add (continuousAt_pi.mp hflow 0)
    have hgc : ContinuousAt (fun z : NormalizedState × ℝ =>
        projectiveActiveWall (normalizedMaxCurve z.1 t₀ z.2)) (x, s + u) :=
      ContinuousAt.comp (g := projectiveActiveWall)
        (f := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (contDiffAt_projectiveActiveWall 1 (ne_of_gt (hreg _ hv).2)).continuousAt hflow
    have hlocal : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, s + u),
        projectiveActiveWall (normalizedMaxCurve z.1 t₀ z.2) = η → z.2 = τ z.1 := by
      by_cases heq : s + u = τ x
      · rw [heq]
        exact huniq.mono fun _ h hhit => (h hhit).symm
      · exact (hgc.eventually_ne (havoid _ ⟨hv.1, lt_of_le_of_ne hv.2 heq⟩)).mono
          fun _ h hhit => (h hhit).elim
    have hdom : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, s + u), z.2 ∈ normalizedMaxDomain z.1 t₀ :=
      (isOpen_normalizedFlowDomain t₀).mem_nhds (hreg _ hv).1
    have hshift : ContinuousAt (fun z : NormalizedState × ℝ => (z.1, s + z.2)) (x, u) :=
      continuousAt_fst.prodMk (continuousAt_const.add continuousAt_snd)
    exact hshift.eventually (hdom.and ((hAc.eventually (isOpen_Ioi.mem_nhds (hreg _ hv).2)).and hlocal))
  filter_upwards [H, hcτ.eventually (isOpen_Ioi.mem_nhds hst), hhit] with y hy hsy hhit_y
  have Ht (t : ℝ) (ht : t ∈ Icc s (τ y)) :
      t ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ t 0 ∧
      (projectiveActiveWall (normalizedMaxCurve y t₀ t) = η → t = τ y) := by
    simpa only [add_sub_cancel] using hy (t - s)
      ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 s⟩
  refine ⟨⟨⟨hsy, (Ht _ ⟨hsy.le, le_rfl⟩).1, hhit_y⟩, ?_⟩,
    fun t ht => ⟨(Ht t ht).1, (Ht t ht).2.1⟩⟩
  intro t ht
  by_contra! hlt
  exact (ne_of_lt hlt) ((Ht t ⟨ht.1.le, hlt.le⟩).2.2 ht.2.2)

theorem exists_activeWall_interior_first_hit_two {x : NormalizedState} {t₀ s t η : ℝ}
    (hst : s < t)
    (hreg : ∀ u ∈ Icc s t, u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (havoid : ∀ u ∈ Ico s t, projectiveActiveWall (normalizedMaxCurve x t₀ u) ≠ η)
    (hrate : normalizedEventRate projectiveActiveWall x t₀ t < 0)
    (hhit : projectiveActiveWall (normalizedMaxCurve x t₀ t) = η) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
      ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y))) x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x t₀ t) x ∧
      HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y)))
        ((fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)).comp
          (normalizedEventDifferential projectiveActiveWall x t₀ t)) x ∧
      (∀ᶠ y in 𝓝 x,
        IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain y t₀ ∧
          projectiveActiveWall (normalizedMaxCurve y t₀ u) = η} (τ y) ∧
        (∀ u ∈ Icc s (τ y), u ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ u 0) ∧
        normalizedEventRate projectiveActiveWall y t₀ (τ y) < 0) := by
  have hdom := (hreg t ⟨hst.le, le_rfl⟩).1
  have hA := ne_of_gt (hreg t ⟨hst.le, le_rfl⟩).2
  have hg := contDiffAt_projectiveActiveWall 2 hA
  obtain ⟨τ, hτ, hcτ, hdτ, hlocal, huniq, _, hdEnd⟩ := exists_normalized_event hdom
    (contDiffAt_projectiveActiveWall 1 hA) (ne_of_lt hrate)
  let F : NormalizedState × ℝ → NormalizedState := fun z => normalizedMaxCurve z.1 t₀ z.2
  let Q : NormalizedState × ℝ → ℝ := fun z => projectiveActiveWall (F z)
  have hcF : ContDiffAt ℝ 2 F (x, t) := contDiffAt_normalizedMaxCurve_two hdom
  have hcQ : ContDiffAt ℝ 2 Q (x, t) :=
    ContDiffAt.comp (g := projectiveActiveWall) (f := F) (x, t) hg hcF
  have htime : HasDerivAt (fun u => Q (x, u)) (normalizedEventRate projectiveActiveWall x t₀ t) t :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve hdom)
  have hτ2 := contDiffAt_scalar_event_branch_two hcQ htime (ne_of_lt hrate) hτ
    hcτ.continuousAt (hlocal.mono fun _ h => h.2)
  have hcEnd : ContDiffAt ℝ 2 (fun y => F (y, τ y)) x := by
    have H : ContDiffAt ℝ 2 F (x, τ x) := by rw [hτ]; exact hcF
    exact H.comp x (contDiffAt_id.prodMk hτ2)
  have hto : ContDiffAt ℝ 2 toProjectiveState (F (x, τ x)) := by
    rw [hτ]
    exact contDiffAt_toProjectiveState 2 hA
  have hdOut := (hto.differentiableAt (by norm_num)).hasFDerivAt.comp x hdEnd
  rw [hτ] at hdOut
  have Hfirst := eventually_activeWall_interior_first_hit hcτ.continuousAt
    (by rw [hτ]; exact hst) (by simpa only [hτ] using hreg) (by simpa only [hτ] using havoid)
    (hlocal.mono fun _ h => h.2.trans hhit)
    (by rw [hτ]; exact huniq.mono fun _ h hh => h.2.mp (hh.trans hhit.symm))
  have hgraph : Tendsto (fun y => (y, τ y)) (𝓝 x) (𝓝 (x, t)) := by
    simpa only [hτ, id_eq] using (continuousAt_id.prodMk hcτ.continuousAt).tendsto
  have Hrate := hgraph.eventually ((continuousAt_activeWall_event_rate hdom hA).eventually
    (isOpen_Iio.mem_nhds hrate))
  refine ⟨τ, hτ, hτ2,
    ContDiffAt.comp (g := toProjectiveState) (f := fun y => F (y, τ y)) x hto hcEnd, hdτ, hdOut, ?_⟩
  filter_upwards [Hfirst, Hrate] with y hy hr
  exact ⟨hy.1, hy.2, hr⟩

end BianchiIX
