import BianchiIX.Dynamics.DownwardReturnRestart
import BianchiIX.Dynamics.ActiveWallDowncrossing
import BianchiIX.Dynamics.ProjectiveFlowSecondRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- A compact prefix allowing only upward hits stays free of downward hits under a continuous moving cutoff. -/
theorem eventually_projectiveOriginalFlow_no_downward {y : ProjectiveState} {Θ : ProjectiveState → ℝ}
    (hD : 0 < projectiveStateDenom y) (hΘ : ContinuousAt Θ y) (hpos : 0 < Θ y)
    (hreg : ∀ t ∈ Icc 0 (Θ y), t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hbefore : ∀ t ∈ Icc 0 (Θ y), projectiveOriginalFlow y 0 t 2 ≠ 1 ∨
      0 < normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t) :
    ∀ᶠ z in 𝓝 y, ∀ t ∈ Icc 0 (Θ z),
      0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0 ∧
      (projectiveOriginalFlow z 0 t 2 ≠ 1 ∨
        0 < normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t) := by
  apply eventually_forall_movingInterval hΘ hpos
  intro t ht
  obtain ⟨hdom, hA⟩ := hreg t ht
  have hpair : ContinuousAt (fun p : ProjectiveState × ℝ => (fromProjectiveState p.1, p.2)) (y, t) := by
    exact ((contDiffAt_fromProjectiveState 1 hD.ne').continuousAt.comp
      (continuousAt_fst : ContinuousAt (Prod.fst : ProjectiveState × ℝ → ProjectiveState) (y, t))).prodMk continuousAt_snd
  have hflow : ContinuousAt (fun p : ProjectiveState × ℝ =>
      normalizedMaxCurve (fromProjectiveState p.1) 0 p.2) (y, t) :=
    ContinuousAt.comp (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
      (f := fun p : ProjectiveState × ℝ => (fromProjectiveState p.1, p.2))
      (normalizedMaxCurve_regular hdom).2.continuousAt hpair
  have hclock : ContinuousAt (fun p : ProjectiveState × ℝ =>
      1 + normalizedMaxCurve (fromProjectiveState p.1) 0 p.2 0) (y, t) :=
    continuousAt_const.add (continuousAt_pi.mp hflow 0)
  have HA := hclock.eventually (lt_mem_nhds hA)
  rcases hbefore t ht with hv | hr
  · have hp := (contDiffAt_projectiveOriginalFlow_two hD hdom hA).continuousAt
    exact HA.and (((continuousAt_pi.mp hp 2).eventually_ne hv).mono fun _ h => Or.inl h)
  · have hc : ContinuousAt (fun p : ProjectiveState × ℝ =>
        normalizedEventRate projectiveActiveWall (fromProjectiveState p.1) 0 p.2) (y, t) :=
      ContinuousAt.comp (g := fun p : NormalizedState × ℝ => normalizedEventRate projectiveActiveWall p.1 0 p.2)
        (f := fun p : ProjectiveState × ℝ => (fromProjectiveState p.1, p.2))
        (continuousAt_activeWall_event_rate hdom hA.ne') hpair
    exact HA.and ((hc.eventually (lt_mem_nhds hr)).mono fun _ h => Or.inr h)

/-- Event identity, including the exact elapsed time, holds as an ordinary germ for a continuous moving cutoff. -/
theorem partialCoreDownwardReturn_moving_cutoff_eventuallyEq {y : ProjectiveState} {Θ : ProjectiveState → ℝ}
    (hD : 0 < projectiveStateDenom y) (hΘ : ContinuousAt Θ y) (hpos : 0 < Θ y)
    (hreg : ∀ t ∈ Icc 0 (Θ y), t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hbefore : ∀ t ∈ Icc 0 (Θ y), projectiveOriginalFlow y 0 t 2 ≠ 1 ∨
      0 < normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t)
    (Hnear : ∀ᶠ z in 𝓝 (projectiveOriginalFlow y 0 (Θ y)),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreDownwardReturnTime z)) :
    (partialCoreDownwardReturnTime =ᶠ[𝓝 y]
      fun z => Θ z + partialCoreDownwardReturnTime (projectiveOriginalFlow z 0 (Θ z))) ∧
    (partialCoreDownwardReturnState =ᶠ[𝓝 y]
      fun z => partialCoreDownwardReturnState (projectiveOriginalFlow z 0 (Θ z))) := by
  have hc : ContinuousAt (fun z => projectiveOriginalFlow z 0 (Θ z)) y :=
    ContinuousAt.comp (g := fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 0 p.2)
      (f := fun z => (z, Θ z))
      (contDiffAt_projectiveOriginalFlow_two hD (hreg _ ⟨hpos.le, le_rfl⟩).1
        (hreg _ ⟨hpos.le, le_rfl⟩).2).continuousAt (continuousAt_id.prodMk hΘ)
  have H : ∀ᶠ z in 𝓝 y,
      partialCoreDownwardReturnTime z = Θ z + partialCoreDownwardReturnTime (projectiveOriginalFlow z 0 (Θ z)) ∧
      partialCoreDownwardReturnState z = partialCoreDownwardReturnState (projectiveOriginalFlow z 0 (Θ z)) := by
    filter_upwards [continuous_projectiveStateDenom.continuousAt.eventually (lt_mem_nhds hD),
      hΘ.eventually (lt_mem_nhds hpos), eventually_projectiveOriginalFlow_no_downward hD hΘ hpos hreg hbefore,
      hc.tendsto.eventually Hnear] with z hd hp hz hn
    apply (partialCoreDownwardReturn_restart hd hp.le (hz _ ⟨hp.le, le_rfl⟩).1 ?_ hn).2
    intro t ht hhit hnegative
    rcases (hz t ⟨ht.1.le, ht.2⟩).2 with havoid | hpositive
    · exact havoid hhit
    · exact not_lt_of_ge hpositive.le hnegative
  exact ⟨H.mono fun _ h => h.1, H.mono fun _ h => h.2⟩

/-- Freezing a continuous cutoff gives the same C2 event map and differential; no cutoff derivative is needed. -/
theorem partialCoreDownwardReturn_moving_cutoff_regular {y : ProjectiveState} {Θ : ProjectiveState → ℝ}
    (hD : 0 < projectiveStateDenom y) (hΘ : ContinuousAt Θ y) (hpos : 0 < Θ y)
    (hreg : ∀ t ∈ Icc 0 (Θ y), t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0)
    (hbefore : ∀ t ∈ Icc 0 (Θ y), projectiveOriginalFlow y 0 t 2 ≠ 1 ∨
      0 < normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t)
    (Hnear : ∀ᶠ z in 𝓝 (projectiveOriginalFlow y 0 (Θ y)),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreDownwardReturnTime z))
    (hcT : ContDiffAt ℝ 2 partialCoreDownwardReturnTime (projectiveOriginalFlow y 0 (Θ y)))
    (hcE : ContDiffAt ℝ 2 partialCoreDownwardReturnState (projectiveOriginalFlow y 0 (Θ y))) :
    ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
    ContDiffAt ℝ 2 (fun z => Θ z + partialCoreDownwardReturnTime (projectiveOriginalFlow z 0 (Θ z))) y ∧
    ContDiffAt ℝ 2 (fun z => partialCoreDownwardReturnState (projectiveOriginalFlow z 0 (Θ z))) y ∧
    fderiv ℝ (fun z => Θ z + partialCoreDownwardReturnTime (projectiveOriginalFlow z 0 (Θ z))) y =
      fderiv ℝ partialCoreDownwardReturnTime y ∧
    fderiv ℝ (fun z => partialCoreDownwardReturnState (projectiveOriginalFlow z 0 (Θ z))) y =
      fderiv ℝ partialCoreDownwardReturnState y := by
  have HM := partialCoreDownwardReturn_moving_cutoff_eventuallyEq hD hΘ hpos hreg hbefore Hnear
  have HF := partialCoreDownwardReturn_moving_cutoff_eventuallyEq (Θ := fun _ => Θ y)
    hD continuousAt_const hpos hreg hbefore Hnear
  have hflow : ContDiffAt ℝ 2 (fun z => projectiveOriginalFlow z 0 (Θ y)) y :=
    ContDiffAt.comp (g := fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 0 p.2)
      (f := fun z : ProjectiveState => (z, Θ y)) y
      (contDiffAt_projectiveOriginalFlow_two hD (hreg _ ⟨hpos.le, le_rfl⟩).1
        (hreg _ ⟨hpos.le, le_rfl⟩).2) (contDiffAt_id.prodMk contDiffAt_const)
  have hT : ContDiffAt ℝ 2 partialCoreDownwardReturnTime y :=
    (contDiffAt_const.add (ContDiffAt.comp (g := partialCoreDownwardReturnTime) y hcT hflow)).congr_of_eventuallyEq HF.1
  have hE : ContDiffAt ℝ 2 partialCoreDownwardReturnState y :=
    (ContDiffAt.comp (g := partialCoreDownwardReturnState) y hcE hflow).congr_of_eventuallyEq HF.2
  exact ⟨hT, hE, hT.congr_of_eventuallyEq HM.1.symm, hE.congr_of_eventuallyEq HM.2.symm,
    HM.1.fderiv_eq.symm, HM.2.fderiv_eq.symm⟩

end BianchiIX
