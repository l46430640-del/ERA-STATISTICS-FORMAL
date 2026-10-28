import BianchiIX.Dynamics.ConnectionEvents
import BianchiIX.Analysis.FirstReturnPersistence

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem continuousAt_growingWall_event_rate {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) (hA : 1 + normalizedMaxCurve x t₀ t 0 ≠ 0) :
    ContinuousAt (fun z : NormalizedState × ℝ => normalizedEventRate projectiveGrowingWall z.1 t₀ z.2) (x, t) := by
  have hflow := (normalizedMaxCurve_regular ht).2.continuousAt
  have hderiv := (contDiffAt_projectiveGrowingWall 2 hA).continuousAt_fderiv (by norm_num)
  have hderiv' : ContinuousAt (fun z : NormalizedState × ℝ =>
      fderiv ℝ projectiveGrowingWall (normalizedMaxCurve z.1 t₀ z.2)) (x, t) :=
    ContinuousAt.comp (f := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) hderiv hflow
  have hfield : ContinuousAt (fun z : NormalizedState × ℝ =>
      normalizedField (normalizedMaxCurve z.1 t₀ z.2)) (x, t) :=
    ContinuousAt.comp (f := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
      (contDiff_normalizedField 1).continuous.continuousAt hflow
  exact hderiv'.clm_apply hfield

/-- Positive growth on the whole flight persists and makes a nearby event the first hit. -/
theorem eventually_growingWall_first_hit {x : NormalizedState} {τ : NormalizedState → ℝ}
    (hcτ : ContinuousAt τ x) (hT : 0 < τ x)
    (hreg : ∀ t ∈ Icc 0 (τ x), t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0)
    (hrate : ∀ t ∈ Icc 0 (τ x), 0 < normalizedEventRate projectiveGrowingWall x 0 t)
    (hhit : ∀ᶠ y in 𝓝 x, projectiveGrowingWall (normalizedMaxCurve y 0 (τ y)) = 1) :
    ∀ᶠ y in 𝓝 x,
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain y 0 ∧ projectiveGrowingWall (normalizedMaxCurve y 0 t) = 1} (τ y) ∧
      (∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0) ∧
      (∀ t ∈ Ico 0 (τ y), projectiveGrowingWall (normalizedMaxCurve y 0 t) < 1) ∧
      0 < normalizedEventRate projectiveGrowingWall y 0 (τ y) := by
  have hpersist : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc 0 (τ y),
      t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0 ∧
        0 < normalizedEventRate projectiveGrowingWall y 0 t := by
    apply eventually_forall_movingInterval hcτ hT
    intro t ht
    have hflow := (normalizedMaxCurve_regular (hreg t ht).1).2.continuousAt
    have hA : ContinuousAt (fun z : NormalizedState × ℝ => 1 + normalizedMaxCurve z.1 0 z.2 0) (x, t) :=
      continuousAt_const.add (continuousAt_pi.mp hflow 0)
    have hdom : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 0 :=
      (isOpen_normalizedFlowDomain 0).mem_nhds (hreg t ht).1
    exact hdom.and
      ((hA.eventually (isOpen_Ioi.mem_nhds (hreg t ht).2)).and
        ((continuousAt_growingWall_event_rate (hreg t ht).1 (ne_of_gt (hreg t ht).2)).eventually
          (isOpen_Ioi.mem_nhds (hrate t ht))))
  have hpos := hcτ.eventually (isOpen_Ioi.mem_nhds hT)
  filter_upwards [hpersist, hpos, hhit] with y hy hτ hhit_y
  have htmem : τ y ∈ Icc 0 (τ y) := ⟨hτ.le, le_rfl⟩
  have hd (t : ℝ) (ht : t ∈ Icc 0 (τ y)) :
      HasDerivAt (fun s => projectiveGrowingWall (normalizedMaxCurve y 0 s))
        (normalizedEventRate projectiveGrowingWall y 0 t) t := by
    exact ((contDiffAt_projectiveGrowingWall 1 (ne_of_gt (hy t ht).2.1)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve (hy t ht).1)
  have hmono : StrictMonoOn (fun t => projectiveGrowingWall (normalizedMaxCurve y 0 t)) (Icc 0 (τ y)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (HasDerivAt.continuousOn hd)
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact (hy t (interior_subset ht)).2.2
  have hbefore (t : ℝ) (ht : t ∈ Ico 0 (τ y)) : projectiveGrowingWall (normalizedMaxCurve y 0 t) < 1 := by
    simpa only [hhit_y] using hmono ⟨ht.1, ht.2.le⟩ htmem ht.2
  refine ⟨⟨⟨hτ, (hy _ htmem).1, hhit_y⟩, ?_⟩,
    (fun t ht => ⟨(hy t ht).1, (hy t ht).2.1⟩), hbefore, (hy _ htmem).2.2⟩
  intro t ht
  by_contra hnot
  have H := hbefore t ⟨ht.1.le, lt_of_not_ge hnot⟩
  rw [ht.2.2] at H
  exact lt_irrefl _ H

end BianchiIX
