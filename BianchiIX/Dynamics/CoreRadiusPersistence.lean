import BianchiIX.Analysis.FirstReturnPersistence
import BianchiIX.Dynamics.CoreEntryBounds
import BianchiIX.Dynamics.CoreExitEvents

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreRadius_flow_regular {Y : CoreAngleState} {t : ℝ}
    (hk : 1 < Y 0) (hD : 0 < projectiveStateDenom (coreRadiusEntry Y))
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0) :
    (∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, t),
      q.2 ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry q.1)) 0 ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry q.1)) 0 q.2 0) ∧
      ContinuousAt (fun q : CoreAngleState × ℝ => projectiveOriginalFlow (coreRadiusEntry q.1) 0 q.2) (Y, t) := by
  have hc := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).comp Y
    (contDiffAt_coreRadiusEntry 1 hk)).continuousAt
  have hpair : ContinuousAt (fun q : CoreAngleState × ℝ =>
      (fromProjectiveState (coreRadiusEntry q.1), q.2)) (Y, t) := by
    convert! (hc.comp (continuousAt_fst : ContinuousAt (Prod.fst : CoreAngleState × ℝ → CoreAngleState)
      (Y, t))).prodMk continuousAt_snd using 1
  have hflow : ContinuousAt (fun q : CoreAngleState × ℝ =>
      normalizedMaxCurve (fromProjectiveState (coreRadiusEntry q.1)) 0 q.2) (Y, t) := by
    exact ContinuousAt.comp (g := fun q : NormalizedState × ℝ => normalizedMaxCurve q.1 0 q.2)
      (f := fun q : CoreAngleState × ℝ => (fromProjectiveState (coreRadiusEntry q.1), q.2))
      (normalizedMaxCurve_regular ht).2.continuousAt hpair
  have hclock : ContinuousAt (fun q : CoreAngleState × ℝ =>
      1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry q.1)) 0 q.2 0) (Y, t) :=
    continuousAt_const.add (continuousAt_pi.mp hflow 0)
  refine ⟨(hpair.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds ht)).and
    (hclock.eventually (isOpen_Ioi.mem_nhds hA)), ?_⟩
  exact ContinuousAt.comp (g := toProjectiveState)
    (f := fun q : CoreAngleState × ℝ => normalizedMaxCurve (fromProjectiveState (coreRadiusEntry q.1)) 0 q.2)
    (contDiffAt_toProjectiveState 1 (ne_of_gt hA)).continuousAt hflow

theorem coreRadiusEntry_transverse {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    0 < projectiveField (coreRadiusEntry Y) 2 := by
  have hgap := coreRadiusEntry_gap hk
  have hc := (core_section_coupling_bound hk hu hw).2
  change 0 < (1 + Real.sqrt (Y 0 ^ 2 - 1) - 1 - coupling (Y 1) 1 (Y 2)) * 1
  linarith only [hgap, hc, hk]

/-- The incoming section fixes the locally unique active-wall crossing at time zero. -/
theorem eventually_coreRadius_entry_unique {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, 0),
      projectiveOriginalFlow (coreRadiusEntry q.1) 0 q.2 2 = 1 → q.2 = 0 := by
  have hD : 0 < projectiveStateDenom (coreRadiusEntry Y) :=
    (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := (contDiffAt_coreRadiusEntry 1 (by linarith only [hk] : 1 < Y 0)).continuousAt
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have htrans : projectiveField (projectiveOriginalFlow (coreRadiusEntry Y) 0 0) 2 ≠ 0 := by
    rw [projectiveOriginalFlow_initial hD]
    exact ne_of_gt (coreRadiusEntry_transverse hk hu hw)
  obtain ⟨σ, _, _, _, huniq, _, _⟩ := exists_projectiveWall_event hD
    (initial_mem_normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Y)) 0) hA htrans
  have hbase : projectiveOriginalFlow (coreRadiusEntry Y) 0 0 2 = 1 := by
    rw [projectiveOriginalFlow_initial hD]
    rfl
  have hpair : ContinuousAt (fun q : CoreAngleState × ℝ => (coreRadiusEntry q.1, q.2)) (Y, 0) := by
    convert! (hc.comp (continuousAt_fst : ContinuousAt (Prod.fst : CoreAngleState × ℝ → CoreAngleState)
      (Y, 0))).prodMk continuousAt_snd using 1
  have hlocal : ∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, 0),
      projectiveOriginalFlow (coreRadiusEntry q.1) 0 q.2 2 = 1 ↔ σ (coreRadiusEntry q.1) = q.2 := by
    filter_upwards [hpair.eventually huniq] with q hq
    simpa only [hbase] using hq.2
  have hDnear : ∀ᶠ Z in 𝓝 Y, 0 < projectiveStateDenom (coreRadiusEntry Z) :=
    (continuous_projectiveStateDenom.continuousAt.comp hc).eventually (isOpen_Ioi.mem_nhds hD)
  have hzero : ∀ᶠ Z in 𝓝 Y, σ (coreRadiusEntry Z) = 0 := by
    have hz : ContinuousAt (fun Z : CoreAngleState => (Z, (0 : ℝ))) Y :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hz.eventually hlocal, hDnear] with Z hZ hDZ
    apply hZ.mp
    rw [projectiveOriginalFlow_initial hDZ]
    rfl
  have hf : ContinuousAt (Prod.fst : CoreAngleState × ℝ → CoreAngleState) (Y, 0) := continuousAt_fst
  filter_upwards [hlocal, hf.eventually hzero] with q hq hq0
  intro heq
  exact (hq.mp heq).symm.trans hq0

/-- A continuous exit branch near a transverse core traversal is the actual first return. -/
theorem eventually_coreRadius_firstReturn {Y : CoreAngleState} {τ : CoreAngleState → ℝ} {T : ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) (hT : 0 < T)
    (hτ : τ Y = T) (hcτ : ContinuousAt τ Y)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T)
    (hcore : ∀ t ∈ Icc 0 T,
      0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 t 0 ∧
        coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t))
    (hhit : ∀ᶠ Z in 𝓝 Y, projectiveOriginalFlow (coreRadiusEntry Z) 0 (τ Z) 2 = 1)
    (huniq : ∀ᶠ q : CoreAngleState × ℝ in 𝓝 (Y, T),
      projectiveOriginalFlow (coreRadiusEntry q.1) 0 q.2 2 = 1 → τ q.1 = q.2) :
    ∀ᶠ Z in 𝓝 Y,
      IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 = 1} (τ Z) ∧
        ∀ t ∈ Icc 0 (τ Z), t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0 ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Z)) 0 t 0 := by
  have hD : 0 < projectiveStateDenom (coreRadiusEntry Y) :=
    (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu hw)).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  have hpos : 0 < τ Y := by rw [hτ]; exact hT
  have hreg (t : ℝ) (ht : t ∈ Icc 0 T) := coreRadius_flow_regular
    (by linarith only [hk] : 1 < Y 0) hD
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1) (hcore t ht).1
  have hregular : ∀ᶠ Z in 𝓝 Y, ∀ t ∈ Icc 0 (τ Z),
      t ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry Z)) 0 ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Z)) 0 t 0 := by
    apply eventually_forall_movingInterval hcτ hpos
    intro t ht
    rw [hτ] at ht
    exact (hreg t ht).1
  have hno : ∀ᶠ Z in 𝓝 Y, ∀ t ∈ Ioo 0 (τ Z), projectiveOriginalFlow (coreRadiusEntry Z) 0 t 2 ≠ 1 := by
    apply eventually_no_intermediate_return hcτ hpos (eventually_coreRadius_entry_unique hk hu hw)
    · rw [hτ]
      exact huniq.mono fun _ h heq => (h heq).symm
    · intro t ht
      rw [hτ] at ht
      exact continuousAt_pi.mp (hreg t ⟨ht.1.le, ht.2.le⟩).2 2
    · intro t ht heq
      rw [hτ] at ht
      exact (not_le_of_gt ht.2) (hfirst.2 ⟨ht.1, heq⟩)
  filter_upwards [hregular, hno, hhit, hcτ.eventually (isOpen_Ioi.mem_nhds hpos)] with Z hr hn hh hp
  refine ⟨⟨⟨hp, hh⟩, ?_⟩, hr⟩
  intro t ht
  by_contra! hlt
  exact hn t ⟨ht.1, hlt⟩ ht.2

end BianchiIX
