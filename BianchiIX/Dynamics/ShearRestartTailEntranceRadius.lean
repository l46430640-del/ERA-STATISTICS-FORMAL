import BianchiIX.Dynamics.ShearRestartTailEntranceInputs
import BianchiIX.Dynamics.ShearRestartTailProjectionPhase
import BianchiIX.Dynamics.EntranceLogWeightedRadius

noncomputable section

namespace BianchiIX

open Set

/-- The actual first upward return preserves the large radius and its ordinary radial response. -/
theorem exists_restartShearTail_entrance_radius :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
            let k := fun r => coreRadius (Y r 0) (Y r 2)
            let κ := fun r => coreRadius (entranceReturnState (Y r) 0) (entranceReturnState (Y r) 2)
            entranceReturnValid (Y ρ) ∧ ContDiffAt ℝ 2 entranceReturnTime (Y ρ) ∧
            ContDiffAt ℝ 2 entranceReturnState (Y ρ) ∧
            DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ k ρ ∧
            1 / (48 * a) ≤ κ ρ ∧ κ ρ ≤ 128 / a ∧ 1 / (48 * a) ≤ k ρ ∧
            |κ ρ - k ρ| ≤ C * a ∧ |deriv κ ρ - deriv k ρ| ≤ C / a ∧
            |deriv k ρ| ≤ 6144 / a ^ 2 := by
  obtain ⟨A, hA, δ, hδ, hδsmall, HA⟩ := exists_entrance_log_weighted_radius
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_entrance_inputs
  obtain ⟨hF, hhF, HF⟩ := exists_restartShearTail_projection_phase
  refine ⟨min hI hF, lt_min hhI hhF, ?_⟩
  intro h hh q D hq hD
  obtain ⟨B, hB, HB⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨_, _, HΦ⟩ := HF h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D hq hD
  let C := 24 * A + 64 * A * B + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCA : 24 * A ≤ C := by dsimp only [C]; linarith only [mul_pos hA hB]
  have hCAB : 64 * A * B ≤ C := by dsimp only [C]; linarith only [hA]
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨aI, haI, HAI⟩ := HB P hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aF, haF, HAF⟩ := HΦ P hP
  refine ⟨min aI aF, lt_min haI haF, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y k κ
  obtain ⟨HY, hk8, hklo, hkhi, hm, hu, hv, hw, Hsmall, Hdm, Hdwall⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, HfD, _, _, Hflo, Hfhi⟩ :=
    HAF a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  let f := restartShearTailProjectionPhase h a q ζ ν (shearTailTime a D)
  have hk0 : 0 < k ρ := by change 8 ≤ k ρ at hk8; linarith only [hk8]
  have hk' : 7 / 4 ≤ k ρ := by change 8 ≤ k ρ at hk8; linarith only [hk8]
  have hu' : 0 ≤ Y ρ 1 ∧ Y ρ 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hδsmall⟩
  have hw' : 0 ≤ Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hδsmall⟩
  obtain ⟨Hvalid, Htime, Hstate, _⟩ := entranceReturn_regular hk' hm.le hu' hv hw'
  have Hreg := entranceReturn_region hk' hm.le hu' hv hw' _ ⟨Hvalid.1.1.1.le, le_rfl⟩
  change entranceRegion (k ρ) (entranceReturnState (Y ρ)) at Hreg
  have Hκscale : 99 / 100 * k ρ ≤ κ ρ ∧ κ ρ ≤ 101 / 100 * k ρ := by
    have H := abs_le.mp Hreg.2.1
    change -(k ρ / 100) ≤ κ ρ - k ρ ∧ κ ρ - k ρ ≤ k ρ / 100 at H
    constructor <;> linarith only [H.1, H.2]
  have HL : 1 ≤ 1 + |Real.log a| := by linarith only [abs_nonneg (Real.log a)]
  obtain ⟨HκD, HkD, Hvalue, Hder⟩ := HA Y ρ B (1 + |Real.log a|) HY hB.le HL hk8 hm.le hu hv hw
    Hsmall Hdm Hdwall
  have HKlo : 1 / (48 * a) ≤ k ρ := by
    exact (div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1])
      (by linarith only [ha.1])).trans hklo
  have Hκlo : 1 / (48 * a) ≤ κ ρ := by
    calc
      _ = (1 / 2) * (1 / (24 * a)) := by ring
      _ ≤ (1 / 2) * k ρ := mul_le_mul_of_nonneg_left hklo (by norm_num)
      _ ≤ _ := by linarith only [Hκscale.1, hk0]
  have Hκhi : κ ρ ≤ 128 / a := by
    calc
      _ ≤ 2 * k ρ := by linarith only [Hκscale.2, hk0]
      _ ≤ 2 * (64 / a) := mul_le_mul_of_nonneg_left hkhi (by norm_num)
      _ = _ := by ring
  have HV : |κ ρ - k ρ| ≤ C * a := Hvalue.trans (by
    calc
      _ ≤ A / (1 / (24 * a)) := div_le_div_of_nonneg_left hA.le (by positivity [ha.1]) hklo
      _ = 24 * A * a := by field_simp [ha.1.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_right hCA ha.1.le)
  have HD : |deriv κ ρ - deriv k ρ| ≤ C / a := Hder.trans (by
    calc
      _ ≤ A * B * (64 / a) := mul_le_mul_of_nonneg_left hkhi (mul_nonneg hA.le hB.le)
      _ = (64 * A * B) / a := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hCAB ha.1.le)
  have hf0 : 0 < f ρ := div_pos (by norm_num) hk0
  have Hfscale : a / 32 ≤ f ρ := by
    calc
      _ = 2 / (64 / a) := by field_simp [ha.1.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hk0 hkhi
  have Hfabs : |deriv f ρ| ≤ 3 := by
    have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
    have hsqrt0 : 0 < Real.sqrt (3 : ℝ) := by positivity
    rw [abs_of_nonneg (by exact (by positivity : 0 ≤ 1 / (4 * Real.sqrt (3 : ℝ))).trans Hflo)]
    have H := div_le_self (by norm_num : (0 : ℝ) ≤ 2) hsqrt1
    linarith only [H, Hfhi]
  have heq : k = fun r => 2 / f r := by
    funext r
    change coreRadius (Y r 0) (Y r 2) = 2 / (2 / coreRadius (Y r 0) (Y r 2))
    simp
  have Hkd : |deriv k ρ| ≤ 6144 / a ^ 2 := by
    rw [heq, deriv_const_div 2 HfD hf0.ne', abs_div, abs_mul, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_nonneg (sq_nonneg (f ρ))]
    calc
      _ ≤ (2 * 3) / (f ρ) ^ 2 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left Hfabs (by norm_num)) (sq_nonneg _)
      _ ≤ (2 * 3) / (a / 32) ^ 2 := div_le_div_of_nonneg_left (by norm_num)
        (by positivity [ha.1]) (pow_le_pow_left₀ (by positivity [ha.1]) Hfscale 2)
      _ = _ := by ring
  exact ⟨Hvalid, Htime, Hstate, HκD, HkD, Hκlo, Hκhi, HKlo, HV, HD, Hkd⟩

end BianchiIX
