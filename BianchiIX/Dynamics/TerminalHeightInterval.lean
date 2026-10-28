import BianchiIX.Dynamics.ExitCycleHeightUniform
import BianchiIX.Dynamics.TerminalHeightFreezing

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem exists_terminal_cycle_entrance_inputs_uniform {εin η₀ : ℝ} (hεin : 0 < εin)
    (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100) {q J : ℕ} (hJ : q + 2 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → η ≤ εin / (4 * (11 / 5) ^ q) →
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := projectiveCycle (coreTailState h Y)
      let k := coreRadius (z 0) (z 2)
      let γ := normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0
      coreTailValid h Y ∧ toProjectiveState (γ (coreTailTime h Y)) = z ∧
        7 / 4 < k ∧ 2 < z 0 ∧
        (0 < z 1 ∧ z 1 ≤ εin ∧ z 1 * k ^ q ≤ εin / 2) ∧
        (0 < z 2 ∧ z 2 < 1 / 2) ∧
        (0 < z 3 ∧ z 3 ≤ εin ∧ z 3 * k ^ q ≤ εin / 2) ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y), 0 < 1 + γ t 0 ∧ |toProjectiveState (γ t) 2| ≤ 1 / 5000) ∧
        0 < projectiveCycleDenom (coreTailState h Y) := by
  obtain ⟨C, hC, ε₀, hε₀, HE⟩ := exists_terminal_axisCycle_endpoint_uniform hη₀ (by omega : 2 ≤ J)
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let δ := εin / (4 * (11 / 5 : ℝ) ^ q)
  have hδ : 0 < δ := div_pos hεin (by positivity)
  let ε := min ε₀ (δ / C)
  refine ⟨ε, lt_min hε₀ (div_pos hδ hC0), ?_⟩
  intro η α b u w hηlo hηhi hηin hα hb hsmall hsum hu hw Y h z k γ
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hα0 : 0 < α := hα.1
  have hsmall₀ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₀ (δ / C)) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, HEq, HH, HM, HK, HU, HW, HP, HF, _⟩ := HE η α b u w hηlo hηhi hα hb hsmall₀ hsum
  have hbudget : C * b ≤ δ * α ^ (2 * J) := by
    have Hε := (le_div_iff₀ hC0).mp (min_le_right ε₀ (δ / C))
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hC0.le,
      mul_le_mul_of_nonneg_right Hε (pow_nonneg hα.1.le (2 * J))]
  have hlow : (19 / 10 : ℝ) ≤ 19 / (10 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.2]
  have hk : 7 / 4 < k := by dsimp only [k, z]; linarith only [HK.1, hlow]
  have hm : 2 < z 0 := by dsimp only [z]; linarith only [HM.1, hlow]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hkc : k ≤ (11 / 5) / α := HK.2.le.trans_eq (by ring)
  have hU : 0 < z 1 := lt_of_lt_of_le (mul_pos (div_pos hη (by norm_num)) (pow_pos hα.1 (J - 2))) HU.1
  have hpos : 0 < z 2 ∧ 0 < z 3 := HP ⟨hu, hw⟩
  have hPu := (exitCycle_entrance_power hα hk0 hkc hη.le hηin HU.2 hJ).2
  have hWpower : z 3 ≤ 2 * δ * α ^ (2 * J - 2) :=
    (le_abs_self _).trans (HW.2.trans (exitCycle_scaled_wall_power hα.1 (by omega) hbudget))
  have hPw := (exitCycle_entrance_power hα hk0 hkc hδ.le le_rfl hWpower (by omega : q + 2 ≤ 2 * J)).2
  have hkp : 1 ≤ k ^ q := one_le_pow₀ (by linarith only [hk] : 1 ≤ k)
  have hsmallwall {a : ℝ} (ha : 0 < a) (hP : a * k ^ q ≤ εin / 2) : a ≤ εin := by
    nlinarith only [mul_le_mul_of_nonneg_left hkp ha.le, hP, hεin]
  have ht : coreTailTime h Y ∈ Icc 0 (coreTailTime h Y) := ⟨HV.1.1.1.le, le_rfl⟩
  have hvbound := (HF _ ht).2
  rw [HEq] at hvbound
  exact ⟨HV, HEq, hk, hm, ⟨hU, hsmallwall hU hPu, hPu⟩,
    ⟨hpos.1, by linarith only [le_abs_self (z 2), hvbound]⟩,
    ⟨hpos.2, hsmallwall hpos.2 hPw, hPw⟩, HF, lt_trans (by positivity) HH.1⟩

/-- All admissible heights above one fixed lower height share a single original entrance domain. -/
theorem exists_terminal_connection_height_interval {εin η₀ : ℝ}
    (hεin : 0 < εin ∧ εin ≤ 1 / 10000) (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {q J : ℕ} (hJ : q + 2 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → η ≤ εin / (4 * (11 / 5) ^ q) →
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let x := axisCycle (fromProjectiveState (coreTailEntry Y))
      coreTailValid h Y ∧ entranceReturnValid (projectiveCycle (coreTailState h Y)) ∧
        (ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionTime p.1 p.2) (h, Y) ∧
          ContDiffAt ℝ 2 (fun p : ℝ × CoreAngleState => terminalConnectionState p.1 p.2) (h, Y) ∧
          (∀ᶠ p : ℝ × CoreAngleState in 𝓝 (h, Y),
            terminalConnectionTime p.1 p.2 = terminalConnectionTime h p.2 ∧
            terminalConnectionState p.1 p.2 = terminalConnectionState h p.2)) ∧
        IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
          projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} (terminalConnectionTime h Y) ∧
        toProjectiveState (normalizedMaxCurve x 0 (terminalConnectionTime h Y)) = terminalConnectionState h Y := by
  obtain ⟨ε, hε, HE⟩ := exists_terminal_cycle_entrance_inputs_uniform hεin.1 hη₀ hJ
  refine ⟨ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hηin hα hb hsmall hsum hu hw Y h x
  obtain ⟨HV, HEq, HK, HM, HU, HVa, HW, HF, HH⟩ := HE η α b u w hηlo hηhi hηin hα hb hsmall hsum hu hw
  let z := projectiveCycle (coreTailState h Y)
  have hpow : 1 ≤ coreRadius (z 0) (z 2) ^ q := one_le_pow₀ (by linarith only [HK])
  have HU' : z 1 < 1 / 10000 := by
    have H := mul_le_mul_of_nonneg_left hpow HU.1.le
    nlinarith only [H, HU.2.2, hεin.2]
  have HW' : z 3 < 1 / 10000 := by
    have H := mul_le_mul_of_nonneg_left hpow HW.1.le
    nlinarith only [H, HW.2.2, hεin.2]
  have Hprefix (t : ℝ) (ht : t ∈ Icc 0 (coreTailTime h Y)) :
      0 < 1 + normalizedMaxCurve x 0 t 0 ∧ projectiveActiveWall (normalizedMaxCurve x 0 t) < 1 := by
    refine ⟨(HF t ht).1, ?_⟩
    have Hb := (HF t ht).2
    change toProjectiveState _ 2 < 1
    linarith only [le_abs_self (toProjectiveState (normalizedMaxCurve x 0 t) 2), Hb]
  have Hregular := terminalConnection_joint_regular_height_independent
    (by change 1 < 2 + 2 * α; linarith only [hα.1]) HV HH Hprefix
    HK (by linarith only [HM]) ⟨HU.1, HU'⟩ ⟨HVa.1, by linarith only [HVa.2]⟩ ⟨HW.1, HW'⟩
  have hc : stateConstraint x = 1 := by
    rw [axisCycle_constraint]
    exact fromProjectiveState_constraint (coreTailValid_denom_pos HV).ne'
  have HA := entranceReturn_existing_orbit hc HV.1.1.1.le HEq Hprefix HK.le
    (by linarith only [HM]) ⟨HU.1.le, HU'.le⟩ ⟨HVa.1, by linarith only [HVa.2]⟩ ⟨HW.1.le, HW'.le⟩
  exact ⟨HV, HA.1, Hregular, HA.2.2.2.1, HA.2.2.2.2.2.2.1⟩

/-- A whole prescribed interval, rather than two prechosen heights, gives the same physical map. -/
theorem exists_terminal_connection_uniform_height_independent {εin η₀ η₁ : ℝ}
    (hεin : 0 < εin ∧ εin ≤ 1 / 10000) (hη₀ : 0 < η₀)
    (hη₀₁ : η₀ ≤ η₁) (hη₁ : η₁ ≤ 1 / 100)
    {q J : ℕ} (hJ : q + 2 ≤ J) (hηin : η₁ ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      ∀ η ∈ Icc η₀ η₁,
        terminalConnectionTime (η * α ^ J) Y = terminalConnectionTime (η₀ * α ^ J) Y ∧
        terminalConnectionState (η * α ^ J) Y = terminalConnectionState (η₀ * α ^ J) Y := by
  obtain ⟨ε, hε, HE⟩ := exists_terminal_connection_height_interval hεin ⟨hη₀, hη₀₁.trans hη₁⟩ hJ
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y η hη
  have H := HE η α b u w hη.1 (hη.2.trans hη₁) (hη.2.trans hηin) hα hb hsmall hsum hu hw
  have H₀ := HE η₀ α b u w le_rfl (hη₀₁.trans hη₁) (hη₀₁.trans hηin) hα hb hsmall hsum hu hw
  have heq := H.2.2.2.1.unique H₀.2.2.2.1
  refine ⟨heq, H.2.2.2.2.symm.trans ?_⟩
  rw [heq]
  exact H₀.2.2.2.2

end BianchiIX
