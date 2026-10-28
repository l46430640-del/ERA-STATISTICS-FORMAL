import BianchiIX.Analysis.FirstReturnPersistence
import BianchiIX.Dynamics.ReferenceSectionMap

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem contDiffAt_referenceCoreChart {k : ℝ} (hk : 1 < k) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n coreSectionChart (referenceCoreInput k) := by
  have hf := contDiffAt_fromProjectiveState n
    (ne_of_gt (referencePulse_denom_pos k (-referenceHalfTime k)))
  rw [← referenceCoreInput_embedding hk] at hf
  exact hf.comp _ (contDiff_coreSectionEmbedding n).contDiffAt

theorem eventually_referenceCore_chart_denom_pos {k : ℝ} (hk : 1 < k) :
    ∀ᶠ z in 𝓝 (referenceCoreInput k), 0 < projectiveStateDenom (coreSectionEmbedding z) := by
  have hc : Continuous (fun z => projectiveStateDenom (coreSectionEmbedding z)) :=
    continuous_projectiveStateDenom.comp (contDiff_coreSectionEmbedding 1).continuous
  apply hc.continuousAt.eventually (isOpen_Ioi.mem_nhds _)
  change 0 < projectiveStateDenom (coreSectionEmbedding (referenceCoreInput k))
  rw [referenceCoreInput_embedding hk]
  exact referencePulse_denom_pos k _

theorem referenceCore_interval_regular {k t : ℝ} (hk : 1 < k)
    (ht : t ∈ Icc 0 (referenceNormalizedTime k)) :
    t ∈ normalizedMaxDomain (coreSectionChart (referenceCoreInput k)) 0 ∧
      0 < 1 + normalizedMaxCurve (coreSectionChart (referenceCoreInput k)) 0 t 0 := by
  have hc : Continuous (referenceClock k) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_referenceClock k s).continuousAt
  have hends : -referenceHalfTime k ≤ referenceHalfTime k := by
    linarith [referenceHalfTime_pos hk]
  have hm : t ∈ Icc (referenceClock k (-referenceHalfTime k))
      (referenceClock k (referenceHalfTime k)) := by
    simpa only [referenceClock_entry, referenceClock_exit] using ht
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc hends hc.continuousOn hm
  rw [referenceCoreInput_chart hk, ← hs]
  exact ⟨(referenceClock_normalized_orbit k s).1, referenceClock_chart_pos k s⟩

theorem continuousAt_coreSection_pair {z : CoreCoordinates} {t : ℝ}
    (hc : ContinuousAt coreSectionChart z) :
    ContinuousAt (fun q : CoreCoordinates × ℝ => (coreSectionChart q.1, q.2)) (z, t) := by
  have hfst : ContinuousAt (fun q : CoreCoordinates × ℝ => coreSectionChart q.1) (z, t) := by
    have hf : ContinuousAt (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates) (z, t) := continuousAt_fst
    exact ContinuousAt.comp (f := (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates))
      (g := coreSectionChart) hc hf
  exact hfst.prodMk continuousAt_snd

theorem continuousAt_coreFlow {z : CoreCoordinates} {t : ℝ}
    (hc : ContinuousAt coreSectionChart z)
    (ht : t ∈ normalizedMaxDomain (coreSectionChart z) 0) :
    ContinuousAt (fun q : CoreCoordinates × ℝ =>
      normalizedMaxCurve (coreSectionChart q.1) 0 q.2) (z, t) := by
  exact ContinuousAt.comp (g := fun q : NormalizedState × ℝ => normalizedMaxCurve q.1 0 q.2)
    (f := fun q : CoreCoordinates × ℝ => (coreSectionChart q.1, q.2))
    (normalizedMaxCurve_regular ht).2.continuousAt (continuousAt_coreSection_pair hc)

theorem referenceEntryState_rate_pos {k : ℝ} (hk : 1 < k) :
    fderiv ℝ projectiveActiveWall (referenceEntryState k) (normalizedField (referenceEntryState k)) > 0 := by
  have hA : 0 < 1 + referenceEntryState k 0 :=
    fromProjectiveState_clock_pos (referencePulse_denom_pos k _)
  have hc : stateConstraint (referenceEntryState k) = 1 :=
    fromProjectiveState_constraint (ne_of_gt (referencePulse_denom_pos k _))
  rw [projectiveActiveWall_fderiv_field (ne_of_gt hA) hc]
  have hproj : toProjectiveState (referenceEntryState k) = referencePulse k (-referenceHalfTime k) :=
    toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k _))
  rw [hproj, referencePulse_entry hk]
  simpa [projectiveField, activeVelocity, coupling] using mul_pos hA (referenceCoreGap_pos hk)

/-- The section itself fixes the locally unique entry event at time zero. -/
theorem eventually_referenceCore_entry_unique {k : ℝ} (hk : 1 < k) :
    ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (referenceCoreInput k, 0),
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart q.1) 0 q.2) = 1 → q.2 = 0 := by
  let z₀ := referenceCoreInput k
  have hbase := referenceCoreInput_chart hk
  have hchart := (contDiffAt_referenceCoreChart hk 1).continuousAt
  have hA : 0 < 1 + referenceEntryState k 0 :=
    fromProjectiveState_clock_pos (referencePulse_denom_pos k _)
  have hg : ContDiffAt ℝ 1 projectiveActiveWall (normalizedMaxCurve (referenceEntryState k) 0 0) := by
    rw [normalizedMaxCurve_initial]
    exact contDiffAt_projectiveActiveWall 1 (ne_of_gt hA)
  have hr : normalizedEventRate projectiveActiveWall (referenceEntryState k) 0 0 ≠ 0 := by
    simpa only [normalizedEventRate, normalizedMaxCurve_initial] using
      ne_of_gt (referenceEntryState_rate_pos hk)
  have hv : projectiveActiveWall (normalizedMaxCurve (referenceEntryState k) 0 0) = 1 := by
    rw [normalizedMaxCurve_initial]
    unfold projectiveActiveWall referenceEntryState
    rw [toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k _)),
      referencePulse_entry hk]
    rfl
  obtain ⟨T, _, _, _, _, huniq, _, _⟩ :=
    exists_normalized_event (initial_mem_normalizedMaxDomain (referenceEntryState k) 0) hg hr
  have hmap : ContinuousAt (fun q : CoreCoordinates × ℝ => (coreSectionChart q.1, q.2)) (z₀, 0) :=
    continuousAt_coreSection_pair hchart
  have hlocal : ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (z₀, 0),
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart q.1) 0 q.2) = 1 ↔
        T (coreSectionChart q.1) = q.2 := by
    have H := hmap.eventually (hbase.symm ▸ huniq)
    filter_upwards [H] with q hq
    simpa only [hbase, hv] using hq.2
  have hzero : ∀ᶠ z in 𝓝 z₀, T (coreSectionChart z) = 0 := by
    have hzmap : ContinuousAt (fun z : CoreCoordinates => (z, (0 : ℝ))) z₀ :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hzmap.eventually hlocal, eventually_referenceCore_chart_denom_pos hk] with z hz hdz
    apply hz.mp
    rw [normalizedMaxCurve_initial]
    unfold projectiveActiveWall coreSectionChart
    rw [toProjectiveState_fromProjectiveState (ne_of_gt hdz)]
    rfl
  have hzprod : ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (z₀, 0), T (coreSectionChart q.1) = 0 := by
    have hf : ContinuousAt (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates) (z₀, 0) := continuousAt_fst
    exact hf.eventually hzero
  filter_upwards [hlocal, hzprod] with q hq hz
  intro heq
  exact (hq.mp heq).symm.trans hz

/-- The whole moving flight segment remains in the original flow and projective chart. -/
theorem eventually_referenceCore_interval_regular {k : ℝ} (hk : 1 < k)
    {tau : CoreCoordinates → ℝ}
    (hτ : tau (referenceCoreInput k) = referenceNormalizedTime k)
    (hcτ : ContinuousAt tau (referenceCoreInput k)) :
    ∀ᶠ z in 𝓝 (referenceCoreInput k), ∀ t ∈ Icc 0 (tau z),
      t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
        0 < 1 + normalizedMaxCurve (coreSectionChart z) 0 t 0 := by
  apply eventually_forall_movingInterval hcτ (by rw [hτ]; exact referenceNormalizedTime_pos hk)
  intro t ht
  rw [hτ] at ht
  obtain ⟨hdom, hpos⟩ := referenceCore_interval_regular hk ht
  have hc := (contDiffAt_referenceCoreChart hk 1).continuousAt
  have hflow := continuousAt_coreFlow hc hdom
  have hA : ContinuousAt (fun q : CoreCoordinates × ℝ =>
      1 + normalizedMaxCurve (coreSectionChart q.1) 0 q.2 0) (referenceCoreInput k, t) :=
    continuousAt_const.add (continuousAt_pi.mp hflow 0)
  have hd : ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (referenceCoreInput k, t),
      q.2 ∈ normalizedMaxDomain (coreSectionChart q.1) 0 :=
    (continuousAt_coreSection_pair hc).eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hdom)
  exact hd.and (hA.eventually (isOpen_Ioi.mem_nhds hpos))

theorem eventually_referenceCore_no_intermediate_return {k : ℝ} (hk : 1 < k)
    {tau : CoreCoordinates → ℝ}
    (hτ : tau (referenceCoreInput k) = referenceNormalizedTime k)
    (hcτ : ContinuousAt tau (referenceCoreInput k))
    (huniq : ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (referenceCoreInput k, referenceNormalizedTime k),
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart q.1) 0 q.2) = 1 → tau q.1 = q.2) :
    ∀ᶠ z in 𝓝 (referenceCoreInput k), ∀ t ∈ Ioo 0 (tau z),
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t) ≠ 1 := by
  apply eventually_no_intermediate_return hcτ (by rw [hτ]; exact referenceNormalizedTime_pos hk)
    (eventually_referenceCore_entry_unique hk)
  · rw [hτ]
    exact huniq.mono fun _ h heq => (h heq).symm
  · intro t ht
    rw [hτ] at ht
    obtain ⟨hdom, hpos⟩ := referenceCore_interval_regular hk ⟨ht.1.le, ht.2.le⟩
    have hflow := continuousAt_coreFlow (contDiffAt_referenceCoreChart hk 1).continuousAt hdom
    exact ContinuousAt.comp (f := fun q : CoreCoordinates × ℝ =>
      normalizedMaxCurve (coreSectionChart q.1) 0 q.2) (g := projectiveActiveWall)
      (contDiffAt_projectiveActiveWall 1 (ne_of_gt hpos)).continuousAt hflow
  · intro t ht
    rw [hτ] at ht
    have H := (referencePulse_normalized_crossing hk).2.2 t ht
    apply ne_of_gt
    simpa only [projectiveActiveWall, referenceCoreInput_chart hk, referenceEntryState,
      referencePulse_entry hk] using H

theorem eventually_referenceCore_above_section {k : ℝ} (hk : 1 < k)
    {tau : CoreCoordinates → ℝ}
    (hτ : tau (referenceCoreInput k) = referenceNormalizedTime k)
    (hcτ : ContinuousAt tau (referenceCoreInput k))
    (huniq : ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (referenceCoreInput k, referenceNormalizedTime k),
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart q.1) 0 q.2) = 1 → tau q.1 = q.2) :
    ∀ᶠ z in 𝓝 (referenceCoreInput k), ∀ t ∈ Ioo 0 (tau z),
      1 < projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t) := by
  have hmid : referenceNormalizedTime k / 2 ∈ Ioo 0 (referenceNormalizedTime k) := by
    constructor <;> linarith [referenceNormalizedTime_pos hk]
  obtain ⟨hdom, hpos⟩ := referenceCore_interval_regular hk ⟨hmid.1.le, hmid.2.le⟩
  have hflow := continuousAt_coreFlow (contDiffAt_referenceCoreChart hk 1).continuousAt hdom
  have hobs : ContinuousAt (fun q : CoreCoordinates × ℝ =>
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart q.1) 0 q.2))
      (referenceCoreInput k, referenceNormalizedTime k / 2) :=
    ContinuousAt.comp (f := fun q : CoreCoordinates × ℝ => normalizedMaxCurve (coreSectionChart q.1) 0 q.2)
      (g := projectiveActiveWall) (contDiffAt_projectiveActiveWall 1 (ne_of_gt hpos)).continuousAt hflow
  have hv : 1 < projectiveActiveWall
      (normalizedMaxCurve (coreSectionChart (referenceCoreInput k)) 0 (referenceNormalizedTime k / 2)) := by
    simpa only [projectiveActiveWall, referenceCoreInput_chart hk, referenceEntryState,
      referencePulse_entry hk] using (referencePulse_normalized_crossing hk).2.2 _ hmid
  have hgraph : Tendsto (fun z : CoreCoordinates => (z, tau z / 2))
      (𝓝 (referenceCoreInput k)) (𝓝 (referenceCoreInput k, referenceNormalizedTime k / 2)) := by
    have H : ContinuousAt (fun z : CoreCoordinates => (z, tau z / 2)) (referenceCoreInput k) :=
      continuousAt_id.prodMk (hcτ.div_const 2)
    simpa only [hτ] using H.tendsto
  have hmiddle := hgraph.eventually (hobs.eventually (isOpen_Ioi.mem_nhds hv))
  have hpositive : ∀ᶠ z in 𝓝 (referenceCoreInput k), 0 < tau z :=
    hcτ.eventually (isOpen_Ioi.mem_nhds (by rw [hτ]; exact referenceNormalizedTime_pos hk))
  filter_upwards [hmiddle, hpositive, eventually_referenceCore_interval_regular hk hτ hcτ,
    eventually_referenceCore_no_intermediate_return hk hτ hcτ huniq] with z hm hp hreg hno
  apply strict_above_of_no_return (m := tau z / 2) ?_ (by constructor <;> linarith) hm hno
  intro t ht
  obtain ⟨hd, hA⟩ := hreg t ⟨ht.1.le, ht.2.le⟩
  exact (ContinuousAt.comp (f := normalizedMaxCurve (coreSectionChart z) 0) (g := projectiveActiveWall)
    (contDiffAt_projectiveActiveWall 1 (ne_of_gt hA)).continuousAt
    (hasDerivAt_normalizedMaxCurve hd).continuousAt).continuousWithinAt

/-- Near each reference pulse, the differentiable exit map is the actual first positive return. -/
theorem exists_referenceCore_firstReturn {k : ℝ} (hk : 1 < k) :
    ∃ (tau : CoreCoordinates → ℝ) (P : CoreCoordinates → CoreCoordinates),
      tau (referenceCoreInput k) = referenceNormalizedTime k ∧
      P (referenceCoreInput k) = referenceCoreOutput k ∧
      ContDiffAt ℝ 1 tau (referenceCoreInput k) ∧ ContDiffAt ℝ 1 P (referenceCoreInput k) ∧
      (∀ᶠ z in 𝓝 (referenceCoreInput k),
        IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t) = 1} (tau z) ∧
        (∀ t ∈ Icc 0 (tau z), t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          0 < 1 + normalizedMaxCurve (coreSectionChart z) 0 t 0) ∧
        (∀ t ∈ Ioo 0 (tau z), 1 < projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t)) ∧
        normalizedEventRate projectiveActiveWall (coreSectionChart z) 0 (tau z) < 0 ∧
        toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (tau z)) = coreSectionEmbedding (P z)) ∧
      (∀ v : CoreCoordinates, fderiv ℝ P (referenceCoreInput k) v =
        ![-v 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * v 1,
          Real.exp (-k * Real.arcosh k) * v 1, Real.exp (-4 * Real.arcosh k / k) * v 2]) := by
  obtain ⟨tau, P, hτ, hP, hcτ, hcP, hhit, huniq, hdP⟩ := exists_referenceCore_section_event hk
  have habove := eventually_referenceCore_above_section hk hτ hcτ.continuousAt
    (huniq.mono fun _ h => h.2.mp)
  have hregular := eventually_referenceCore_interval_regular hk hτ hcτ.continuousAt
  have hdir : ∀ᶠ z in 𝓝 (referenceCoreInput k), projectiveField (coreSectionEmbedding (P z)) 2 < 0 := by
    have hemb : ContinuousAt (fun z => coreSectionEmbedding (P z)) (referenceCoreInput k) :=
      ContinuousAt.comp (f := P) (g := coreSectionEmbedding)
        (contDiff_coreSectionEmbedding 1).continuous.continuousAt hcP.continuousAt
    have hf : ContinuousAt (fun z => projectiveField (coreSectionEmbedding (P z))) (referenceCoreInput k) :=
      ContinuousAt.comp (f := fun z => coreSectionEmbedding (P z)) (g := projectiveField)
        (contDiff_projectiveField 1).continuous.continuousAt hemb
    apply (continuousAt_pi.mp hf 2).eventually (isOpen_Iio.mem_nhds _)
    change projectiveField (coreSectionEmbedding (P (referenceCoreInput k))) 2 < 0
    rw [hP]
    have heq : coreSectionEmbedding (referenceCoreOutput k) = referencePulse k (referenceHalfTime k) := by
      rw [referencePulse_exit hk]
      rfl
    rw [heq, referencePulse_exit_field hk]
    exact neg_neg_of_pos (referenceCoreGap_pos hk)
  refine ⟨tau, P, hτ, hP, hcτ, hcP, ?_, hdP⟩
  filter_upwards [hhit, habove, hregular, hdir, eventually_referenceCore_chart_denom_pos hk]
    with z hz hhigh hreg hdown hD
  refine ⟨⟨⟨hz.1, hz.2.1, ?_⟩, ?_⟩, hreg, hhigh, ?_, hz.2.2⟩
  · change toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (tau z)) 2 = 1
    rw [hz.2.2]
    rfl
  · intro t ht
    by_contra! hlt
    exact (ne_of_gt (hhigh t ⟨ht.1, hlt⟩)) ht.2.2
  · have hA := (hreg (tau z) ⟨hz.1.le, le_rfl⟩).2
    have hc : stateConstraint (normalizedMaxCurve (coreSectionChart z) 0 (tau z)) = 1 := by
      rw [normalizedMaxCurve_constraint hz.2.1]
      exact fromProjectiveState_constraint (ne_of_gt hD)
    rw [normalizedEventRate, projectiveActiveWall_fderiv_field (ne_of_gt hA) hc, hz.2.2]
    exact mul_neg_of_pos_of_neg hA hdown

end BianchiIX
