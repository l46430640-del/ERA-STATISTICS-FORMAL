import BianchiIX.Dynamics.ShearRestartTailEntranceCone
import BianchiIX.Algebra.EntranceConeScaling

noncomputable section

namespace BianchiIX

open Set

/-- The full long-tail entrance cone retains the square root of the active wall and the explicit logarithmic loss. -/
theorem exists_restartShearTail_entrance_weighted_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ A > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
            let Z := fun r => entranceReturnState (Y r)
            let κ := restartShearTailEntranceRadius h a q D ζ ν
            let L := 1 + |Real.log a|
            DifferentiableAt ℝ Z ρ ∧ DifferentiableAt ℝ κ ρ ∧
            0 < -deriv κ ρ ∧ 0 < Z ρ 1 ∧ 0 < Z ρ 3 ∧
            |deriv (fun r => Z r 1) ρ| ≤ A * L * Real.sqrt (Y ρ 1 * Y ρ 2) * Real.sqrt (Z ρ 1) * |deriv κ ρ| ∧
            |deriv (fun r => Z r 3) ρ| ≤ A * L * Real.sqrt (Y ρ 3 * Y ρ 2) * Real.sqrt (Z ρ 3) * |deriv κ ρ| := by
  obtain ⟨C, hC, δ, hδ, hδsmall, HC⟩ := exists_entrance_wall_sqrt_curve_bounds
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_entrance_inputs
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_entrance_phase
  refine ⟨min hI hR, lt_min hhI hhR, ?_⟩
  intro h hh q D hq hD
  obtain ⟨B, hB, HBI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨_, _, HBR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D hq hD
  let A := 36864 * 64 ^ 2 * C * B
  refine ⟨A, by dsimp only [A]; positivity, ?_⟩
  intro P hP
  obtain ⟨aI, haI, HAI⟩ := HBI P hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aR, haR, HAR⟩ := HBR P hP
  refine ⟨min aI aR, lt_min haI haR, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y Z κ L
  obtain ⟨HY, hk8, _, hkhi, hm, hu, hv, hw, _, Hd0, Hdwall⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, _, HK, _, _, Hlo, _⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  let k := coreRadius (Y ρ 0) (Y ρ 2)
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [abs_nonneg (Real.log a)]
  have hL0 : 0 ≤ L := by linarith only [hL]
  change 8 ≤ k at hk8
  change k ≤ 64 / a at hkhi
  change 1 / (36864 * a ^ 2) ≤ -deriv κ ρ at Hlo
  have Hd0' : |deriv (fun r => Y r 0) ρ| ≤ (B * L) * k ^ 2 := Hd0.trans (by
    have H := mul_le_mul_of_nonneg_left hL (mul_nonneg hB.le (sq_nonneg k))
    nlinarith only [H])
  obtain ⟨HZ, hU, hW, HU, HW⟩ := HC Y ρ (B * L) HY (mul_nonneg hB.le hL0)
    (by change 7 / 4 ≤ k; linarith only [hk8]) hm.le hu hv hw Hd0'
    (fun i hi => by simpa only [mul_assoc] using Hdwall i hi)
  have Hcone := entrance_wall_radius_cone hC.le (mul_nonneg hB.le hL0)
    (by linarith only [hk8] : 1 ≤ k)
    (by norm_num : (0 : ℝ) < 36864) ha.1 hkhi (Hlo.trans (neg_le_abs _)) HU HW
  refine ⟨HZ, HK, (by positivity [ha.1] : 0 < 1 / (36864 * a ^ 2)).trans_le Hlo, hU, hW, ?_⟩
  simpa only [A, Z, mul_assoc] using Hcone

end BianchiIX
