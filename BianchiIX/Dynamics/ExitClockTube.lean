import BianchiIX.Dynamics.ExitTailReturnDifferential
import BianchiIX.Analysis.IntervalNeighborhood

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def exitEntryFlow (p : ExitTailState × ℝ) : ProjectiveState :=
  projectiveOriginalFlow (coreTailEntry p.1) 0 p.2

def exitEntryClock (p : ExitTailState × ℝ) : ℝ := exitLogClock (exitEntryFlow p)

def exitEntryRegular (Y : ExitTailState) (t : ℝ) : Prop :=
  1 < Y 0 ∧ 0 < projectiveStateDenom (coreTailEntry Y) ∧
    t ∈ normalizedMaxDomain (fromProjectiveState (coreTailEntry Y)) 0 ∧
    0 < 1 + normalizedMaxCurve (fromProjectiveState (coreTailEntry Y)) 0 t 0 ∧
    0 < exitEntryFlow (Y, t) 2 ∧ exitEntryFlow (Y, t) 0 < 1 ∧
    0 < exitClockRate (exitEntryFlow (Y, t))

theorem contDiffAt_exitEntryFlow_two {Y : ExitTailState} {t : ℝ} (H : exitEntryRegular Y t) :
    ContDiffAt ℝ 2 exitEntryFlow (Y, t) := by
  have hmap : ContDiffAt ℝ 2 (fun p : ExitTailState × ℝ => (coreTailEntry p.1, p.2)) (Y, t) :=
    ((contDiffAt_coreTailEntry 2 H.1).comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have HF := (contDiffAt_projectiveOriginalFlow_two H.2.1 H.2.2.1 H.2.2.2.1).comp (Y, t) hmap
  exact HF

theorem contDiffAt_exitEntryClock_two {Y : ExitTailState} {t : ℝ} (H : exitEntryRegular Y t) :
    ContDiffAt ℝ 2 exitEntryClock (Y, t) :=
  (contDiffAt_exitLogClock 2 H.2.2.2.2.1).comp (Y, t) (contDiffAt_exitEntryFlow_two H)

theorem hasDerivAt_exitEntryClock {Y : ExitTailState} {t : ℝ} (H : exitEntryRegular Y t) :
    HasDerivAt (fun r => exitEntryClock (Y, r)) (exitOriginalClockRate (exitEntryFlow (Y, t))) t := by
  have hflow := hasDerivAt_projectiveOriginalFlow_time H.2.1 H.2.2.1 H.2.2.2.1
  have hclock := ((contDiffAt_exitLogClock 1 H.2.2.2.2.1).differentiableAt (by norm_num)).hasFDerivAt
  have HC := hclock.comp_hasDerivAt t hflow
  change HasDerivAt (fun r => exitEntryClock (Y, r))
    (fderiv ℝ exitLogClock (exitEntryFlow (Y, t)) (projectiveOriginalField (exitEntryFlow (Y, t)))) t at HC
  rwa [exitLogClock_fderiv_field H.2.2.2.2.1] at HC

theorem exitEntryRegular_rate_pos {Y : ExitTailState} {t : ℝ} (H : exitEntryRegular Y t) :
    0 < exitOriginalClockRate (exitEntryFlow (Y, t)) := by
  change 0 < exitOriginalClockRate (projectiveOriginalFlow (coreTailEntry Y) 0 t)
  rw [exitOriginalClockRate_normalized H.2.1 H.2.2.1 H.2.2.2.1]
  exact mul_pos H.2.2.2.1 H.2.2.2.2.2.2

theorem isOpen_exitEntryRegular : IsOpen {p : ExitTailState × ℝ | exitEntryRegular p.1 p.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have he := contDiffAt_coreTailEntry 2 hp.1
  have hentry : ContDiffAt ℝ 2 (fun q : ExitTailState × ℝ => coreTailEntry q.1) p :=
    he.comp p contDiffAt_fst
  have hparam : ContDiffAt ℝ 2 (fun q : ExitTailState × ℝ =>
      (fromProjectiveState (coreTailEntry q.1), q.2)) p := by
    have HF := (contDiffAt_fromProjectiveState 2 hp.2.1.ne').comp p hentry
    exact HF.prodMk contDiffAt_snd
  have hN : ContinuousAt (fun q : ExitTailState × ℝ =>
      normalizedMaxCurve (fromProjectiveState (coreTailEntry q.1)) 0 q.2) p := by
    exact ((contDiffAt_normalizedMaxCurve_two hp.2.2.1).comp p hparam).continuousAt
  have hflow := (contDiffAt_exitEntryFlow_two hp).continuousAt
  have hR : ContinuousAt (fun q : ExitTailState × ℝ => q.1 0) p := by fun_prop
  have hden := continuous_projectiveStateDenom.continuousAt.comp hentry.continuousAt
  have hdom := hparam.continuousAt.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hp.2.2.1)
  have hA : ContinuousAt (fun q : ExitTailState × ℝ =>
      1 + normalizedMaxCurve (fromProjectiveState (coreTailEntry q.1)) 0 q.2 0) p :=
    continuousAt_const.add (continuousAt_pi.mp hN 0)
  have hrate := (contDiff_exitClockRate 1).continuous.continuousAt.comp hflow
  filter_upwards [hR.eventually (isOpen_Ioi.mem_nhds hp.1),
    hden.eventually (isOpen_Ioi.mem_nhds hp.2.1), hdom,
    hA.eventually (isOpen_Ioi.mem_nhds hp.2.2.2.1),
    (continuousAt_pi.mp hflow 2).eventually (isOpen_Ioi.mem_nhds hp.2.2.2.2.1),
    (continuousAt_pi.mp hflow 0).eventually (isOpen_Iio.mem_nhds hp.2.2.2.2.2.1),
    hrate.eventually (isOpen_Ioi.mem_nhds hp.2.2.2.2.2.2)] with q hqR hqD hqd hqA hqV hqM hqrate
  exact ⟨hqR, hqD, hqd, hqA, hqV, hqM, hqrate⟩

/-- A common open parameter and time tube contains a whole regular flight, including both endpoints. -/
theorem exists_exitEntry_regular_tube {Y : ExitTailState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc 0 T, exitEntryRegular Y t) :
    ∃ U : Set ExitTailState, IsOpen U ∧ Y ∈ U ∧ ∃ l r : ℝ,
      l < 0 ∧ T < r ∧ ∀ Z ∈ U, ∀ t ∈ Ioo l r, exitEntryRegular Z t := by
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) : ∀ᶠ s in 𝓝 t, exitEntryRegular Y s :=
    (continuousAt_const.prodMk continuousAt_id).eventually (isOpen_exitEntryRegular.mem_nhds (H t ht))
  obtain ⟨l, r, hl, hr, hinterval⟩ := exists_Ioo_covering_of_eventually hT htime
  let a := l / 2
  let b := (T + r) / 2
  have ha : l < a ∧ a < 0 := by dsimp only [a]; constructor <;> linarith only [hl]
  have hb : T < b ∧ b < r := by dsimp only [b]; constructor <;> linarith only [hr]
  have hcompact : ∀ᶠ Z in 𝓝 Y, ∀ t ∈ Icc a b, exitEntryRegular Z t := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hreg := hinterval t ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
    exact isOpen_exitEntryRegular.mem_nhds hreg
  obtain ⟨U, hU, hUopen, hYU⟩ := mem_nhds_iff.mp hcompact
  exact ⟨U, hUopen, hYU, a, b, ha.2, hb.1, fun Z hZ t ht => hU hZ t (Ioo_subset_Icc_self ht)⟩

theorem exitEntryClock_strictMonoOn {Y : ExitTailState} {I : Set ℝ}
    (hI : Convex ℝ I) (H : ∀ t ∈ I, exitEntryRegular Y t) :
    StrictMonoOn (fun t => exitEntryClock (Y, t)) I := by
  apply strictMonoOn_of_deriv_pos hI (HasDerivAt.continuousOn (fun t ht => hasDerivAt_exitEntryClock (H t ht)))
  intro t ht
  rw [(hasDerivAt_exitEntryClock (H t (interior_subset ht))).deriv]
  exact exitEntryRegular_rate_pos (H t (interior_subset ht))

end BianchiIX
