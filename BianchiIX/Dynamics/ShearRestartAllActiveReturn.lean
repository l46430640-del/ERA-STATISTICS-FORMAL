import BianchiIX.Dynamics.ShearRestartEntranceConnectionCurve
import BianchiIX.Dynamics.ShearRestartReturnCone

noncomputable section

namespace BianchiIX

open Set

/-- The fixed shear return is jointly C2 throughout the positive-wall annulus, without an active-wall cutoff. -/
theorem exists_restartShearReturn_all_active_joint_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
            ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) := by
  obtain ⟨hU, hhU, HU⟩ := exists_restartShearReturn_joint_regular
  obtain ⟨hL, hhL, HL⟩ := exists_restartShearEntrance_connection
  refine ⟨min hU hL, lt_min hhU hhL, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aU, haU, HaU⟩ := HU h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aL, haL, HaL⟩ := HL h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aU aL, lt_min haU haL, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s
  by_cases hv : 1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2
  · obtain ⟨_, hp, hG, hphase, ht⟩ :=
      HaU a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ hv
    exact ⟨hp, hG, hphase, ht⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hp, hG, hphase, ht⟩ :=
      HaL a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ (lt_of_not_ge hv)
    exact ⟨hp, hG, hphase, ht⟩

/-- On the entire positive-wall shear annulus, the fixed return preserves the cone
and its reciprocal phase has strictly positive ordinary radial derivative. -/
theorem exists_restartShearReturn_all_active_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let G := restartShearReturnState h s n₂ n₃
            let g := fun r => G r 0
            ContDiffAt ℝ 2 G ρ ∧ deriv g ρ < 0 ∧
              (∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ|) ∧
              ContDiffAt ℝ 2 (restartShearReturnPhase h s n₂ n₃) ρ ∧
              0 < deriv (restartShearReturnPhase h s n₂ n₃) ρ := by
  obtain ⟨hU, hhU, HU⟩ := exists_restartShearReturn_cone
  obtain ⟨hL, hhL, HL⟩ := exists_restartShearEntrance_connection_curve
  refine ⟨min hU hL, lt_min hhU hhL, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aU, haU, HaU⟩ := HU h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aL, haL, HaL⟩ := HL h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aU aL, lt_min haU haL, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s G g
  have H : ContDiffAt ℝ 2 G ρ ∧ deriv g ρ < 0 ∧
      ∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ| := by
    by_cases hv : 1 ≤ restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2
    · obtain ⟨hc, hneg, hU, hW⟩ :=
        HaU a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ hv
      refine ⟨hc, hneg, ?_⟩
      intro i
      fin_cases i
      · exact hU
      · exact hW
    · obtain ⟨hc, _, _, _, _, hneg, _, _, hcone, _⟩ :=
        HaL a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ (lt_of_not_ge hv)
      exact ⟨hc, hneg, hcone⟩
  have hg0 : g ρ ≠ 0 := by
    change phaseNorm (-connectionReturnState (restartShearReturnParameters h s n₂ n₃ ρ) 0 - 1) 1 ≠ 0
    exact ne_of_gt (by unfold phaseNorm; positivity)
  have hg : ContDiffAt ℝ 2 g ρ := contDiffAt_pi.mp H.1 0
  exact ⟨H.1, H.2.1, H.2.2, contDiffAt_const.div hg hg0,
    reciprocal_curve_derivative_pos (hg.differentiableAt (by norm_num)) hg0 H.2.1⟩

end BianchiIX
