import BianchiIX.Dynamics.TerminalConnection
import BianchiIX.Dynamics.EntranceCoreWalls

noncomputable section

namespace BianchiIX

open Set

/-- The actual terminal connection returns both positive walls to the required core power neighborhood. -/
theorem exists_terminal_connection_core_walls {εin η : ℝ} (hεin : 0 < εin ∧ εin ≤ 1 / 10000)
    (hη : 0 < η ∧ η ≤ 1 / 100) {q J : ℕ} (hq : 16 ≤ q) (hJ : q + 2 ≤ J)
    (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let x := axisCycle (fromProjectiveState (coreTailEntry Y))
      let T := terminalConnectionTime h Y
      let Z := terminalConnectionState h Y
      let κ := coreRadius (Z 0) (Z 2)
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
        projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
        toProjectiveState (normalizedMaxCurve x 0 T) = Z ∧ Z 2 = 1 ∧
        (0 < Z 1 ∧ Z 1 ≤ εin / κ ^ 16) ∧ (0 < Z 3 ∧ Z 3 ≤ εin / κ ^ 16) := by
  obtain ⟨ε₁, hε₁, HE₁⟩ := exists_terminal_cycle_entrance_inputs hεin.1 hη hJ hηin
  obtain ⟨ε₂, hε₂, HE₂⟩ := exists_terminal_connection_first_arrival hεin hη hJ hηin
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h x T Z κ
  have hsmall₁ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₁ ε₂) (pow_nonneg hα.1.le (2 * J)))
  have hsmall₂ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right ε₁ ε₂) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨_, _, HK, HM, HU, HV, HW, _, _⟩ := HE₁ α b u w hα hb hsmall₁ hsum hu hw
  obtain ⟨_, _, _, _, _, HF, _, _, Hstate, Hactive, _⟩ := HE₂ α b u w hα hb hsmall₂ hsum hu hw
  have H := entranceReturn_core_wall_budget hq HK.le (by linarith only [HM])
    ⟨HU.1, HU.2.1.trans hεin.2⟩ ⟨HV.1, by linarith only [HV.2]⟩
    ⟨HW.1, HW.2.1.trans hεin.2⟩ HU.2.2 HW.2.2
  exact ⟨HF, Hstate, Hactive, H.2.2.1, H.2.2.2⟩

end BianchiIX
