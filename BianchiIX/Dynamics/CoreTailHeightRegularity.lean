import BianchiIX.Dynamics.ExitTailRegularity
import BianchiIX.Analysis.ImplicitEventFamily

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The canonical downward event is jointly C2 in its height and original initial data. -/
theorem coreTail_joint_regular_of_valid {Y : CoreAngleState} {h : ℝ}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) :
    ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => coreTailTime p.1 p.2) (h, Y) ∧
      ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => coreTailState p.1 p.2) (h, Y) ∧
      (∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y), coreTailValid p.1 p.2) := by
  let c : CoreAngleState → NormalizedState := fun Z => fromProjectiveState (coreTailEntry Z)
  let p₀ : ℝ × CoreAngleState := (h, Y)
  let T := coreTailTime h Y
  have hT : 0 < T := HV.1.1.1
  have hD := coreTailValid_denom_pos HV
  have hc : ContDiffAt ℝ 2 c Y :=
    (contDiffAt_fromProjectiveState 2 hD.ne').comp Y (contDiffAt_coreTailEntry 2 hR)
  have hc' : ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => c p.2) p₀ := hc.comp p₀ contDiffAt_snd
  have hlast := HV.2.1 T ⟨hT.le, le_rfl⟩
  let F : (ℝ × CoreAngleState) × ℝ → NormalizedState := fun z => normalizedMaxCurve (c z.1.2) 0 z.2
  let Q : (ℝ × CoreAngleState) × ℝ → ℝ := fun z => projectiveActiveWall (F z) - z.1.1
  have hF : ContDiffAt ℝ 2 F (p₀, T) := (contDiffAt_normalizedMaxCurve_two hlast.1).comp (p₀, T)
    ((hc'.comp (p₀, T) contDiffAt_fst).prodMk contDiffAt_snd)
  have hQ : ContDiffAt ℝ 2 Q (p₀, T) :=
    (ContDiffAt.comp (g := projectiveActiveWall) (f := F) (p₀, T)
      (contDiffAt_projectiveActiveWall 2 hlast.2.ne') hF).sub
      (contDiffAt_fst.comp (p₀, T) contDiffAt_fst)
  have htime : HasDerivAt (fun t => Q (p₀, t)) (normalizedEventRate projectiveActiveWall (c Y) 0 T) T :=
    (((contDiffAt_projectiveActiveWall 1 hlast.2.ne').differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt T
      (hasDerivAt_normalizedMaxCurve hlast.1)).sub_const h
  have hrate : normalizedEventRate projectiveActiveWall (c Y) 0 T < 0 := HV.2.2.2.1 T ⟨hT.le, le_rfl⟩
  obtain ⟨τ, hτ, hcτ, hhit⟩ := exists_scalar_event_family_two hQ htime hrate.ne
  have hQ0 : Q (p₀, T) = 0 := sub_eq_zero.mpr HV.1.1.2.2
  have hhit' : ∀ᶠ p in 𝓝 p₀, projectiveActiveWall (normalizedMaxCurve (c p.2) 0 (τ p)) = p.1 := by
    filter_upwards [hhit] with p hp
    exact sub_eq_zero.mp (hp.trans hQ0)
  have hpersist : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ Icc 0 (τ p),
      t ∈ normalizedMaxDomain (c p.2) 0 ∧ 0 < 1 + normalizedMaxCurve (c p.2) 0 t 0 ∧
        normalizedEventRate projectiveActiveWall (c p.2) 0 t < 0 ∧
        |toProjectiveState (normalizedMaxCurve (c p.2) 0 t) 3| < 1 / 2 := by
    apply eventually_forall_movingInterval hcτ.continuousAt (by rw [hτ]; exact hT)
    intro t ht
    rw [hτ] at ht
    have hr := HV.2.1 t ht
    have hprojY : ContinuousAt (fun z : (ℝ × CoreAngleState) × ℝ => z.1.2) (p₀, t) :=
      continuousAt_snd.comp continuousAt_fst
    have hparam : ContinuousAt (fun z : (ℝ × CoreAngleState) × ℝ => (c z.1.2, z.2)) (p₀, t) :=
      (ContinuousAt.comp (x := (p₀, t)) (g := c) (f := fun z : (ℝ × CoreAngleState) × ℝ => z.1.2)
        hc.continuousAt hprojY).prodMk continuousAt_snd
    have hflow := (normalizedMaxCurve_regular hr.1).2.continuousAt
    have hA : ContinuousAt (fun z : NormalizedState × ℝ => 1 + normalizedMaxCurve z.1 0 z.2 0) (c Y, t) :=
      continuousAt_const.add (continuousAt_pi.mp hflow 0)
    have hproj : ContinuousAt (fun z : NormalizedState × ℝ => toProjectiveState (normalizedMaxCurve z.1 0 z.2)) (c Y, t) :=
      ContinuousAt.comp (x := (c Y, t)) (g := toProjectiveState)
        (f := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 0 z.2)
        (contDiffAt_toProjectiveState 1 hr.2.ne').continuousAt hflow
    have hdom : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (c Y, t), z.2 ∈ normalizedMaxDomain z.1 0 :=
      (isOpen_normalizedFlowDomain 0).mem_nhds hr.1
    exact hparam.eventually (hdom.and ((hA.eventually (isOpen_Ioi.mem_nhds hr.2)).and
      (((continuousAt_activeWall_event_rate hr.1 hr.2.ne').eventually
        (isOpen_Iio.mem_nhds (HV.2.2.2.1 t ht))).and
          ((continuousAt_pi.mp hproj 3).abs.eventually (isOpen_Iio.mem_nhds (HV.2.2.2.2 t ht))))))
  have hpos : ∀ᶠ p in 𝓝 p₀, 0 < τ p := hcτ.continuousAt.eventually
    (isOpen_Ioi.mem_nhds (by rw [hτ]; exact hT))
  have hnear : ∀ᶠ p in 𝓝 p₀, coreTailTime p.1 p.2 = τ p ∧ coreTailValid p.1 p.2 := by
    filter_upwards [hpersist, hpos, hhit'] with p hp hτp hhitp
    have htmem : τ p ∈ Icc 0 (τ p) := ⟨hτp.le, le_rfl⟩
    have hd (t : ℝ) (ht : t ∈ Icc 0 (τ p)) :
        HasDerivAt (fun s => projectiveActiveWall (normalizedMaxCurve (c p.2) 0 s))
          (normalizedEventRate projectiveActiveWall (c p.2) 0 t) t :=
      ((contDiffAt_projectiveActiveWall 1 (hp t ht).2.1.ne').differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_normalizedMaxCurve (hp t ht).1)
    have hmono : StrictAntiOn (fun t => projectiveActiveWall (normalizedMaxCurve (c p.2) 0 t)) (Icc 0 (τ p)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (HasDerivAt.continuousOn hd)
      intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      exact (hp t (interior_subset ht)).2.2.1
    have hbefore (t : ℝ) (ht : t ∈ Ico 0 (τ p)) : p.1 < projectiveActiveWall (normalizedMaxCurve (c p.2) 0 t) := by
      simpa only [hhitp] using hmono ⟨ht.1, ht.2.le⟩ htmem ht.2
    have hfirst : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (c p.2) 0 ∧
        projectiveActiveWall (normalizedMaxCurve (c p.2) 0 t) = p.1} (τ p) := by
      refine ⟨⟨hτp, (hp _ htmem).1, hhitp⟩, ?_⟩
      intro t ht
      by_contra hn
      have H := hbefore t ⟨ht.1.le, lt_of_not_ge hn⟩
      rw [ht.2.2] at H
      exact lt_irrefl _ H
    have heq : coreTailTime p.1 p.2 = τ p := hfirst.csInf_eq
    refine ⟨heq, ?_⟩
    dsimp only [coreTailValid]
    rw [heq]
    exact ⟨hfirst, (fun t ht => ⟨(hp t ht).1, (hp t ht).2.1⟩), hbefore,
      (fun t ht => (hp t ht).2.2.1), fun t ht => (hp t ht).2.2.2⟩
  have hcTime := hcτ.congr_of_eventuallyEq (hnear.mono fun _ hp => hp.1)
  have hcEnd : ContDiffAt ℝ 2 (fun p => F (p, τ p)) p₀ := by
    have H : ContDiffAt ℝ 2 F (p₀, τ p₀) := by rw [hτ]; exact hF
    exact H.comp p₀ (contDiffAt_id.prodMk hcτ)
  have hcOut : ContDiffAt ℝ 2 (fun p => toProjectiveState (F (p, τ p))) p₀ := by
    have H : ContDiffAt ℝ 2 toProjectiveState (F (p₀, τ p₀)) := by
      rw [hτ]
      exact contDiffAt_toProjectiveState 2 hlast.2.ne'
    exact H.comp p₀ hcEnd
  refine ⟨hcTime, hcOut.congr_of_eventuallyEq ?_, hnear.mono fun _ hp => hp.2⟩
  filter_upwards [hnear] with p hp
  dsimp only [coreTailState, projectiveOriginalFlow, F, c]
  rw [hp.1]

end BianchiIX
