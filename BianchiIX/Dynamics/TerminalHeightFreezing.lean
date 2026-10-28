import BianchiIX.Dynamics.TerminalHeightLocal

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The actual positive-wall terminal domain satisfies the joint local height theorem. -/
theorem exists_terminal_connection_joint_height_regular {εin η : ℝ}
    (hεin : 0 < εin ∧ εin ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 100)
    {q J : ℕ} (hJ : q + 2 ≤ J) (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : CoreAngleState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionTime p.1 p.2) (h, Y) ∧
        ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionState p.1 p.2) (h, Y) ∧
        (∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y),
          terminalConnectionTime p.1 p.2 = terminalConnectionTime h p.2 ∧
          terminalConnectionState p.1 p.2 = terminalConnectionState h p.2) := by
  obtain ⟨ε, hε, HE⟩ := exists_terminal_cycle_entrance_inputs hεin.1 hη hJ hηin
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h
  obtain ⟨HV, _, HK, HM, HU, HVa, HW, HF, HH⟩ := HE α b u w hα hb hsmall hsum hu hw
  let z := projectiveCycle (coreTailState h Y)
  have hk1 : 1 ≤ coreRadius (z 0) (z 2) := by linarith only [HK]
  have hpow : 1 ≤ coreRadius (z 0) (z 2) ^ q := one_le_pow₀ hk1
  have HU' : z 1 < 1 / 10000 := by
    have H := mul_le_mul_of_nonneg_left hpow HU.1.le
    nlinarith only [H, HU.2.2, hεin.2]
  have HW' : z 3 < 1 / 10000 := by
    have H := mul_le_mul_of_nonneg_left hpow HW.1.le
    nlinarith only [H, HW.2.2, hεin.2]
  exact terminalConnection_joint_regular_height_independent
    (by change 1 < 2 + 2 * α; linarith only [hα.1]) HV HH
    (fun t ht => ⟨(HF t ht).1, by
      have Hb := (HF t ht).2
      change toProjectiveState _ 2 < 1
      linarith only [le_abs_self (toProjectiveState (normalizedMaxCurve
        (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 t) 2), Hb]⟩)
    HK (by linarith only [HM]) ⟨HU.1, HU'⟩ ⟨HVa.1, by linarith only [HVa.2]⟩ ⟨HW.1, HW'⟩

/-- Local independence permits freezing even a merely continuous choice of auxiliary height. -/
theorem terminalConnection_freeze_height_of_local {h : ℝ} {Y : CoreAngleState}
    (HT : ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionTime p.1 p.2) (h, Y))
    (HS : ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionState p.1 p.2) (h, Y))
    (HL : ∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y),
      terminalConnectionTime p.1 p.2 = terminalConnectionTime h p.2 ∧
      terminalConnectionState p.1 p.2 = terminalConnectionState h p.2)
    {a : CoreAngleState → ℝ} (ha : ContinuousAt a Y) (haY : a Y = h) :
    (∀ᶠ Z in 𝓝 Y, terminalConnectionTime (a Z) Z = terminalConnectionTime h Z ∧
      terminalConnectionState (a Z) Z = terminalConnectionState h Z) ∧
      ContDiffAt ℝ 2 (fun Z => terminalConnectionTime (a Z) Z) Y ∧
      ContDiffAt ℝ 2 (fun Z => terminalConnectionState (a Z) Z) Y := by
  have hgraph : Tendsto (fun Z => (a Z, Z)) (𝓝 Y) (𝓝 (h, Y)) := by
    simpa only [ContinuousAt, haY, id_eq] using ha.prodMk continuousAt_id
  have HE := hgraph.eventually HL
  have hfixed : ContDiffAt ℝ 2 (fun Z : CoreAngleState => (h, Z)) Y := contDiffAt_const.prodMk contDiffAt_id
  exact ⟨HE, (HT.comp Y hfixed).congr_of_eventuallyEq (HE.mono fun _ hp => hp.1),
    (HS.comp Y hfixed).congr_of_eventuallyEq (HE.mono fun _ hp => hp.2)⟩

/-- Both physical time and endpoint have zero derivative with respect to the auxiliary height. -/
theorem terminalConnection_height_deriv_zero_of_local {h : ℝ} {Y : CoreAngleState}
    (HL : ∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y),
      terminalConnectionTime p.1 p.2 = terminalConnectionTime h p.2 ∧
      terminalConnectionState p.1 p.2 = terminalConnectionState h p.2) :
    HasDerivAt (fun v => terminalConnectionTime v Y) 0 h ∧
      HasDerivAt (fun v => terminalConnectionState v Y) 0 h := by
  have hslice : ContinuousAt (fun v : ℝ => (v, Y)) h := continuousAt_id.prodMk continuousAt_const
  have HE := hslice.eventually HL
  exact ⟨(hasDerivAt_const h (terminalConnectionTime h Y)).congr_of_eventuallyEq
      (HE.mono fun _ hp => hp.1),
    (hasDerivAt_const h (terminalConnectionState h Y)).congr_of_eventuallyEq
      (HE.mono fun _ hp => hp.2)⟩

/-- Formula (D.23), with the logarithmic height used by the tail clock. -/
theorem terminalConnection_logHeight_deriv_zero_of_local {s : ℝ} {Y : CoreAngleState}
    (HL : ∀ᶠ p : ℝ × CoreAngleState in 𝓝 (Real.exp (-s), Y),
      terminalConnectionTime p.1 p.2 = terminalConnectionTime (Real.exp (-s)) p.2 ∧
      terminalConnectionState p.1 p.2 = terminalConnectionState (Real.exp (-s)) p.2) :
    HasDerivAt (fun v => terminalConnectionTime (Real.exp (-v)) Y) 0 s ∧
      HasDerivAt (fun v => terminalConnectionState (Real.exp (-v)) Y) 0 s := by
  have hslice : ContinuousAt (fun v : ℝ => (Real.exp (-v), Y)) s :=
    (Real.continuous_exp.continuousAt.comp
      (continuousAt_id.neg : ContinuousAt (fun v : ℝ => -v) s)).prodMk continuousAt_const
  have HE := hslice.eventually HL
  exact ⟨(hasDerivAt_const s (terminalConnectionTime (Real.exp (-s)) Y)).congr_of_eventuallyEq
      (HE.mono fun _ hp => hp.1),
    (hasDerivAt_const s (terminalConnectionState (Real.exp (-s)) Y)).congr_of_eventuallyEq
      (HE.mono fun _ hp => hp.2)⟩

/-- On the actual domain every continuous height selection has the same C2 germ as the frozen map. -/
theorem exists_terminal_connection_height_freezing {εin η : ℝ}
    (hεin : 0 < εin ∧ εin ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ 1 / 100)
    {q J : ℕ} (hJ : q + 2 ≤ J) (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : CoreAngleState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      HasDerivAt (fun v => terminalConnectionTime v Y) 0 h ∧
        HasDerivAt (fun v => terminalConnectionState v Y) 0 h ∧
        ∀ a : CoreAngleState → ℝ, ContinuousAt a Y → a Y = h →
          (∀ᶠ Z in 𝓝 Y, terminalConnectionTime (a Z) Z = terminalConnectionTime h Z ∧
            terminalConnectionState (a Z) Z = terminalConnectionState h Z) ∧
          ContDiffAt ℝ 2 (fun Z => terminalConnectionTime (a Z) Z) Y ∧
          ContDiffAt ℝ 2 (fun Z => terminalConnectionState (a Z) Z) Y := by
  obtain ⟨ε, hε, HE⟩ := exists_terminal_connection_joint_height_regular hεin hη hJ hηin
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h
  obtain ⟨HT, HS, HL⟩ := HE α b u w hα hb hsmall hsum hu hw
  have HD := terminalConnection_height_deriv_zero_of_local HL
  exact ⟨HD.1, HD.2, fun a ha haY => terminalConnection_freeze_height_of_local HT HS HL ha haY⟩

end BianchiIX
