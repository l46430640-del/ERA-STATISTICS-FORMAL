import BianchiIX.Dynamics.TerminalConnection
import BianchiIX.Dynamics.CoreTailHeightRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreTail_cycle_endpoint {h : ℝ} {Y : CoreAngleState} (HV : coreTailValid h Y)
    (hH : projectiveCycleDenom (coreTailState h Y) ≠ 0) :
    toProjectiveState (normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0
      (coreTailTime h Y)) = projectiveCycle (coreTailState h Y) := by
  let x := fromProjectiveState (coreTailEntry Y)
  let T := coreTailTime h Y
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (coreTailValid_denom_pos HV).ne'
  have ht := HV.2.1 T ⟨HV.1.1.1.le, le_rfl⟩
  have hcycle : normalizedMaxCurve (axisCycle x) 0 T = axisCycle (normalizedMaxCurve x 0 T) :=
    NormalizedSymmetry.cycle.maxCurve ht.1
  change toProjectiveState (normalizedMaxCurve (axisCycle x) 0 T) = _
  rw [hcycle]
  exact toProjectiveState_axisCycle ht.2.ne'
    ((normalizedMaxCurve_forward_of_constraint hc HV.1.1.1.le).2.1) hH

/-- Locally the full physical arrival is C2 and independent of the intermediate height. -/
theorem terminalConnection_joint_regular_height_independent {h : ℝ} {Y : CoreAngleState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hH : 0 < projectiveCycleDenom (coreTailState h Y))
    (hprefix : ∀ t ∈ Icc 0 (coreTailTime h Y),
      0 < 1 + normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 t 0 ∧
      projectiveActiveWall (normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 t) < 1) :
    let z := projectiveCycle (coreTailState h Y)
    7 / 4 < coreRadius (z 0) (z 2) → 1 < z 0 →
    (0 < z 1 ∧ z 1 < 1 / 10000) → (0 < z 2 ∧ z 2 < 1) →
    (0 < z 3 ∧ z 3 < 1 / 10000) →
    ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionTime p.1 p.2) (h, Y) ∧
      ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionState p.1 p.2) (h, Y) ∧
      (∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y),
        terminalConnectionTime p.1 p.2 = terminalConnectionTime h p.2 ∧
        terminalConnectionState p.1 p.2 = terminalConnectionState h p.2) := by
  intro z hk hm hu hv hw
  let p₀ : ℝ × CoreAngleState := (h, Y)
  let c : CoreAngleState → NormalizedState := fun Z => axisCycle (fromProjectiveState (coreTailEntry Z))
  let Z : ℝ × CoreAngleState → ProjectiveState := fun p => projectiveCycle (coreTailState p.1 p.2)
  have HT := coreTail_joint_regular_of_valid hR HV
  have HZ : ContDiffAt ℝ 2 Z p₀ := ContDiffAt.comp (g := projectiveCycle)
    (f := fun p : ℝ × CoreAngleState => coreTailState p.1 p.2) p₀
    (contDiffAt_projectiveCycle 2 hH.ne') HT.2.1
  have HE := entranceReturn_regular hk.le hm.le ⟨hu.1.le, hu.2.le⟩ hv ⟨hw.1.le, hw.2.le⟩
  have Htime : ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => entranceReturnTime (Z p)) p₀ :=
    ContDiffAt.comp (g := entranceReturnTime) (f := Z) p₀ HE.2.1 HZ
  have Hstate : ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => entranceReturnState (Z p)) p₀ :=
    ContDiffAt.comp (g := entranceReturnState) (f := Z) p₀ HE.2.2.1 HZ
  refine ⟨HT.1.add Htime, Hstate, ?_⟩
  have HZ₀ := continuousAt_pi.mp HZ.continuousAt 0
  have HZ₁ := continuousAt_pi.mp HZ.continuousAt 1
  have HZ₂ := continuousAt_pi.mp HZ.continuousAt 2
  have HZ₃ := continuousAt_pi.mp HZ.continuousAt 3
  have HK : ContinuousAt (fun p => coreRadius (Z p 0) (Z p 2)) p₀ :=
    (((HZ₀.sub_const 1).pow 2).add (HZ₂.pow 2)).sqrt
  have Hden : ContinuousAt (fun p : ℝ × CoreAngleState => projectiveCycleDenom (coreTailState p.1 p.2)) p₀ :=
    ((contDiff_projectiveCycleDenom 2).contDiffAt.comp p₀ HT.2.1).continuousAt
  have Hinputs : ∀ᶠ p in 𝓝 p₀,
      coreTailValid p.1 p.2 ∧ 0 < projectiveCycleDenom (coreTailState p.1 p.2) ∧
      7 / 4 ≤ coreRadius (Z p 0) (Z p 2) ∧ 1 ≤ Z p 0 ∧
      (0 ≤ Z p 1 ∧ Z p 1 ≤ 1 / 10000) ∧ (0 < Z p 2 ∧ Z p 2 < 1) ∧
      (0 ≤ Z p 3 ∧ Z p 3 ≤ 1 / 10000) := by
    filter_upwards [HT.2.2, Hden.eventually (isOpen_Ioi.mem_nhds hH),
      HK.eventually (isOpen_Ioi.mem_nhds hk), HZ₀.eventually (isOpen_Ioi.mem_nhds hm),
      HZ₁.eventually (isOpen_Ioo.mem_nhds hu), HZ₂.eventually (isOpen_Ioo.mem_nhds hv),
      HZ₃.eventually (isOpen_Ioo.mem_nhds hw)] with p hp hd hkp hmp hup hvp hwp
    exact ⟨hp, hd, hkp.le, hmp.le, ⟨hup.1.le, hup.2.le⟩, hvp, ⟨hwp.1.le, hwp.2.le⟩⟩
  have hc : ContDiffAt ℝ 2 c Y := axisCycleEquiv.contDiff.contDiffAt.comp Y
    ((contDiffAt_fromProjectiveState 2 (coreTailValid_denom_pos HV).ne').comp Y
      (contDiffAt_coreTailEntry 2 hR))
  have hconstraint : stateConstraint (c Y) = 1 := by
    rw [axisCycle_constraint]
    exact fromProjectiveState_constraint (coreTailValid_denom_pos HV).ne'
  have Hprefix : ∀ᶠ p : ℝ × CoreAngleState in 𝓝 p₀, ∀ t ∈ Icc 0 (coreTailTime p.1 p.2),
      0 < 1 + normalizedMaxCurve (c p.2) 0 t 0 ∧
      projectiveActiveWall (normalizedMaxCurve (c p.2) 0 t) < 1 := by
    apply eventually_forall_movingInterval HT.1.continuousAt HV.1.1.1
    intro t ht
    have hdom := normalizedMaxDomain_contains_Ici_of_constraint hconstraint 0 ht.1
    have hflow := (normalizedMaxCurve_regular hdom).2.continuousAt
    have hA : ContinuousAt (fun w : NormalizedState × ℝ => 1 + normalizedMaxCurve w.1 0 w.2 0) (c Y, t) :=
      continuousAt_const.add (continuousAt_pi.mp hflow 0)
    have hV : ContinuousAt (fun w : NormalizedState × ℝ => projectiveActiveWall (normalizedMaxCurve w.1 0 w.2)) (c Y, t) :=
      ContinuousAt.comp (x := (c Y, t)) (g := projectiveActiveWall)
        (f := fun w : NormalizedState × ℝ => normalizedMaxCurve w.1 0 w.2)
        (contDiffAt_projectiveActiveWall 1 (hprefix t ht).1.ne').continuousAt hflow
    have hparam : ContinuousAt (fun w : (ℝ × CoreAngleState) × ℝ => (c w.1.2, w.2)) (p₀, t) :=
      (ContinuousAt.comp (x := (p₀, t)) (g := c) (f := fun w : (ℝ × CoreAngleState) × ℝ => w.1.2)
        hc.continuousAt (continuousAt_snd.comp continuousAt_fst)).prodMk continuousAt_snd
    exact hparam.eventually ((hA.eventually (isOpen_Ioi.mem_nhds (hprefix t ht).1)).and
      (hV.eventually (isOpen_Iio.mem_nhds (hprefix t ht).2)))
  have Hphysical : ∀ᶠ p : ℝ × CoreAngleState in 𝓝 p₀,
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (c p.2) 0 ∧
        projectiveActiveWall (normalizedMaxCurve (c p.2) 0 t) = 1} (terminalConnectionTime p.1 p.2) ∧
      toProjectiveState (normalizedMaxCurve (c p.2) 0 (terminalConnectionTime p.1 p.2)) =
        terminalConnectionState p.1 p.2 := by
    filter_upwards [Hinputs, Hprefix] with p hp hpp
    have hcp : stateConstraint (c p.2) = 1 := by
      rw [axisCycle_constraint]
      exact fromProjectiveState_constraint (coreTailValid_denom_pos hp.1).ne'
    have HH := entranceReturn_existing_orbit hcp hp.1.1.1.1.le
      (coreTail_cycle_endpoint hp.1 hp.2.1.ne') hpp hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1
      hp.2.2.2.2.2.1 hp.2.2.2.2.2.2
    exact ⟨HH.2.2.2.1, HH.2.2.2.2.2.2.1⟩
  have hfixed : ContinuousAt (fun p : ℝ × CoreAngleState => (h, p.2)) p₀ :=
    continuousAt_const.prodMk continuousAt_snd
  filter_upwards [Hphysical, hfixed.eventually Hphysical] with p hp hf
  have heq := hp.1.unique hf.1
  refine ⟨heq, hp.2.symm.trans ?_⟩
  rw [heq]
  exact hf.2

end BianchiIX
