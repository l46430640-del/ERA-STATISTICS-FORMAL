import BianchiIX.Dynamics.ExitCycleEntranceInputs
import BianchiIX.Dynamics.EntranceReturnOrbit
import BianchiIX.Dynamics.ExitTailRegularity

noncomputable section

namespace BianchiIX

open Set

def terminalConnectionTime (h : ℝ) (Y : ExitTailState) : ℝ :=
  coreTailTime h Y + entranceReturnTime (projectiveCycle (coreTailState h Y))

def terminalConnectionState (h : ℝ) (Y : ExitTailState) : ProjectiveState :=
  entranceReturnState (projectiveCycle (coreTailState h Y))

theorem terminalConnection_regular_of_entrance {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hH : projectiveCycleDenom (coreTailState h Y) ≠ 0) :
    let z := projectiveCycle (coreTailState h Y)
    7 / 4 ≤ coreRadius (z 0) (z 2) → 1 ≤ z 0 →
    (0 ≤ z 1 ∧ z 1 ≤ 1 / 10000) → (0 < z 2 ∧ z 2 < 1) →
    (0 ≤ z 3 ∧ z 3 ≤ 1 / 10000) →
    ContDiffAt ℝ 2 (terminalConnectionTime h) Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y := by
  intro z hk hm hu hv hw
  have HT := coreTail_regular_of_valid hR HV
  have HC := (contDiffAt_projectiveCycle 2 hH).comp Y HT.2.1
  have HE := entranceReturn_regular hk hm hu hv hw
  have Htime : ContDiffAt ℝ 2 (fun Z => entranceReturnTime (projectiveCycle (coreTailState h Z))) Y :=
    ContDiffAt.comp (g := entranceReturnTime) (f := projectiveCycle ∘ coreTailState h) Y HE.2.1 HC
  have Hstate : ContDiffAt ℝ 2 (fun Z => entranceReturnState (projectiveCycle (coreTailState h Z))) Y :=
    ContDiffAt.comp (g := entranceReturnState) (f := projectiveCycle ∘ coreTailState h) Y HE.2.2.1 HC
  exact ⟨HT.1.add Htime, Hstate⟩

/-- The cyclic tail and long entrance compose to the first physical arrival of the next active wall. -/
theorem exists_terminal_connection_first_arrival {εin η : ℝ} (hεin : 0 < εin ∧ εin ≤ 1 / 10000)
    (hη : 0 < η ∧ η ≤ 1 / 100) {q J : ℕ} (hJ : q + 2 ≤ J)
    (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := projectiveCycle (coreTailState h Y)
      let k := coreRadius (z 0) (z 2)
      let x := axisCycle (fromProjectiveState (coreTailEntry Y))
      let T := terminalConnectionTime h Y
      coreTailValid h Y ∧ entranceReturnValid z ∧
        (z 1 * k ^ q ≤ εin / 2 ∧ z 3 * k ^ q ≤ εin / 2) ∧
        ContDiffAt ℝ 2 entranceReturnTime z ∧ ContDiffAt ℝ 2 entranceReturnState z ∧
        IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
          projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
        (∀ t ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve x 0 t 0) ∧
        (∀ t ∈ Ico 0 T, projectiveActiveWall (normalizedMaxCurve x 0 t) < 1) ∧
        toProjectiveState (normalizedMaxCurve x 0 T) = terminalConnectionState h Y ∧
        terminalConnectionState h Y 2 = 1 ∧
        0 < normalizedEventRate projectiveActiveWall x 0 T ∧
        ContDiffAt ℝ 2 (terminalConnectionTime h) Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y := by
  obtain ⟨ε, hε, HE⟩ := exists_terminal_cycle_entrance_inputs hεin.1 hη hJ hηin
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h z k x T
  obtain ⟨HV, HEq, HK, HM, HU, HVa, HW, HF, HH⟩ := HE α b u w hα hb hsmall hsum hu hw
  have hc : stateConstraint x = 1 := by
    rw [axisCycle_constraint]
    exact fromProjectiveState_constraint (coreTailValid_denom_pos HV).ne'
  have H := entranceReturn_existing_orbit hc HV.1.1.1.le HEq
    (fun r hr => ⟨(HF r hr).1, by
      have Hb := (HF r hr).2
      change toProjectiveState (normalizedMaxCurve x 0 r) 2 < 1
      linarith only [le_abs_self (toProjectiveState (normalizedMaxCurve x 0 r) 2), Hb]⟩)
    HK.le (by linarith only [HM]) ⟨HU.1.le, HU.2.1.trans hεin.2⟩
    ⟨HVa.1, by linarith only [HVa.2]⟩ ⟨HW.1.le, HW.2.1.trans hεin.2⟩
  have Hstate : toProjectiveState (normalizedMaxCurve x 0 T) = terminalConnectionState h Y := H.2.2.2.2.2.2.1
  have Hregular := terminalConnection_regular_of_entrance (by change 1 < 2 + 2 * α; linarith only [hα.1]) HV HH.ne'
    HK.le (by linarith only [HM]) ⟨HU.1.le, HU.2.1.trans hεin.2⟩
    ⟨HVa.1, by linarith only [HVa.2]⟩ ⟨HW.1.le, HW.2.1.trans hεin.2⟩
  refine ⟨HV, H.1, ⟨HU.2.2, HW.2.2⟩, H.2.1, H.2.2.1,
    H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2.1, Hstate, ?_, H.2.2.2.2.2.2.2, Hregular⟩
  rw [← Hstate]
  exact H.2.2.2.1.1.2.2

/-- Two admissible auxiliary heights give the same physical time and endpoint on a common initial domain. -/
theorem exists_terminal_connection_height_independent {εin η₁ η₂ : ℝ}
    (hεin : 0 < εin ∧ εin ≤ 1 / 10000)
    (hη₁ : 0 < η₁ ∧ η₁ ≤ 1 / 100) (hη₂ : 0 < η₂ ∧ η₂ ≤ 1 / 100)
    {q J : ℕ} (hJ : q + 2 ≤ J)
    (hη₁in : η₁ ≤ εin / (4 * (11 / 5) ^ q)) (hη₂in : η₂ ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      terminalConnectionTime (η₁ * α ^ J) Y = terminalConnectionTime (η₂ * α ^ J) Y ∧
        terminalConnectionState (η₁ * α ^ J) Y = terminalConnectionState (η₂ * α ^ J) Y := by
  obtain ⟨ε₁, hε₁, HE₁⟩ := exists_terminal_connection_first_arrival hεin hη₁ hJ hη₁in
  obtain ⟨ε₂, hε₂, HE₂⟩ := exists_terminal_connection_first_arrival hεin hη₂ hJ hη₂in
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y
  have hsmall₁ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₁ ε₂) (pow_nonneg hα.1.le (2 * J)))
  have hsmall₂ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right ε₁ ε₂) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨_, _, _, _, _, H₁, _, _, E₁, _⟩ := HE₁ α b u w hα hb hsmall₁ hsum hu hw
  obtain ⟨_, _, _, _, _, H₂, _, _, E₂, _⟩ := HE₂ α b u w hα hb hsmall₂ hsum hu hw
  have htime := H₁.unique H₂
  refine ⟨htime, E₁.symm.trans ?_⟩
  rw [htime]
  exact E₂

end BianchiIX
