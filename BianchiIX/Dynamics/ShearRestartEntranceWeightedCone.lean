import BianchiIX.Dynamics.ShearRestartEntranceCone
import BianchiIX.Algebra.EntranceConeScaling

noncomputable section

namespace BianchiIX

open Set

/-- The fast-cutoff entrance cone retains both weak amplitudes and the active-wall square root. -/
theorem exists_restartShearEntrance_weighted_cone :
    ∃ hstar > (0 : ℝ), ∃ A > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ),
        ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
          let Z := fun r => entranceReturnState (Y r)
          let κ := fun r => coreRadius (Z r 0) (Z r 2)
          Y ρ 2 < 1 → DifferentiableAt ℝ Z ρ ∧ DifferentiableAt ℝ κ ρ ∧
          0 < -deriv κ ρ ∧ 0 < Z ρ 1 ∧ 0 < Z ρ 3 ∧
          |deriv (fun r => Z r 1) ρ| ≤ A * Real.sqrt (Y ρ 1 * Y ρ 2) * Real.sqrt (Z ρ 1) * |deriv κ ρ| ∧
          |deriv (fun r => Z r 3) ρ| ≤ A * Real.sqrt (Y ρ 3 * Y ρ 2) * Real.sqrt (Z ρ 3) * |deriv κ ρ| := by
  obtain ⟨C, hC, δ, hδ, hδsmall, HC⟩ := exists_entrance_wall_sqrt_curve_bounds
  obtain ⟨hI, hhI, B, hB, HI⟩ := exists_restartShearEntrance_differential_inputs
  obtain ⟨hR, hhR, _, _, HR⟩ := exists_restartShearEntrance_radial_response
  let A := 8192 * 32 ^ 2 * C * B
  refine ⟨min hI hR, lt_min hhI hhR, A, by dsimp only [A]; positivity, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aI aR, lt_min haI haR, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y Z κ hv
  obtain ⟨HY, hk8, _, hkhi, hm, hu, hv', hw, _, Hd0, Hdwall⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨HK, _, _, _, _, _, Hlo, _⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let k := coreRadius (Y ρ 0) (Y ρ 2)
  change 8 ≤ k at hk8
  change k ≤ 32 / a at hkhi
  change 1 / (8192 * a ^ 2) ≤ -deriv κ ρ at Hlo
  obtain ⟨HZ, hU, hW, HU, HW⟩ := HC Y ρ B HY hB.le
    (by change 7 / 4 ≤ k; linarith only [hk8]) hm.le hu hv' hw Hd0 Hdwall
  have Hcone := entrance_wall_radius_cone hC.le hB.le
    (by linarith only [hk8] : 1 ≤ k) (by norm_num : (0 : ℝ) < 8192) ha.1 hkhi
    (Hlo.trans (neg_le_abs _)) HU HW
  exact ⟨HZ, HK, (by positivity [ha.1] : 0 < 1 / (8192 * a ^ 2)).trans_le Hlo, hU, hW, Hcone⟩

end BianchiIX
