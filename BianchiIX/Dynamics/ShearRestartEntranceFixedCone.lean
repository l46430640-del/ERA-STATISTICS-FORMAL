import BianchiIX.Dynamics.ShearRestartTailWeightedCone
import BianchiIX.Dynamics.ShearRestartEntranceWeightedCone
import BianchiIX.Analysis.ShearEntranceConePowers

noncomputable section

namespace BianchiIX

open Set

/-- The fixed fast-cutoff exponents give powers twenty-four and two hundred seventy-four in the entrance cone. -/
theorem exists_restartShearEntrance_fixed_cone :
    ∃ hstar > (0 : ℝ), ∃ C > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) →
        (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
        n₃ ≤ a ^ (550 : ℝ) → ∀ ρ ∈ Icc a (2 * a),
        let s := (50 : ℝ) / 2 * Real.log (1 / a)
        let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
        let Z := fun r => entranceReturnState (Y r)
        let κ := fun r => coreRadius (Z r 0) (Z r 2)
        Y ρ 2 < 1 → DifferentiableAt ℝ Z ρ ∧ DifferentiableAt ℝ κ ρ ∧
        0 < -deriv κ ρ ∧ 0 < Z ρ 1 ∧ 0 < Z ρ 3 ∧
        |deriv (fun r => Z r 1) ρ| ≤ C * a ^ 24 * Real.sqrt (Z ρ 1) * |deriv κ ρ| ∧
        |deriv (fun r => Z r 3) ρ| ≤ C * a ^ 274 * Real.sqrt (Z ρ 3) * |deriv κ ρ| := by
  obtain ⟨hC, hhC, A, hA, HC⟩ := exists_restartShearEntrance_weighted_cone
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hC (min hV 1), lt_min hhC (lt_min hhV zero_lt_one), 4 * A, by positivity, ?_⟩
  intro h hh
  obtain ⟨aC, haC, HAC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ 50 550 (by norm_num) (by norm_num)
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ 50 (by norm_num)
  refine ⟨min aC aV, lt_min haC haV, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y Z κ hv
  obtain ⟨HZ, HK, HKneg, hU, hW, HU, HW⟩ :=
    HAC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, _, _, _, hu, hvbounds, hwbounds, _⟩ :=
    HAV a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε 1 n₂ n₃ hε (by norm_num)
      ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ ρ hρ
  have hh1 := hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hu' : Y ρ 1 ≤ 16 * a ^ 48 := by
    have Hu : Y ρ 1 ≤ 8 * h * a ^ (48 : ℕ) := by
      simpa only [show (50 : ℝ) - 2 = 48 by norm_num, Real.rpow_ofNat] using hu.2
    have H := mul_le_mul_of_nonneg_right hh1 (pow_nonneg ha.1.le 48)
    nlinarith only [Hu, H, pow_nonneg ha.1.le 48]
  have hv0 : 0 ≤ Y ρ 2 := (div_nonneg h₂.1.le (by positivity)).trans hvbounds.1
  have hw0 : 0 ≤ Y ρ 3 := (div_nonneg h₃.1.le (by positivity)).trans hwbounds.1
  have hw' : Y ρ 3 ≤ 16 * a ^ 548 := by
    have hn : n₃ ≤ a ^ (550 : ℕ) := by simpa only [Real.rpow_ofNat] using h₃P
    calc
      _ ≤ 16 * n₃ / a ^ 2 := hwbounds.2
      _ ≤ 16 * a ^ 550 / a ^ 2 := by gcongr
      _ = _ := by field_simp
  have Hroot := shear_fast_entrance_cone_powers ⟨hu.1.le, hu'⟩ ⟨hv0, hv.le⟩ ⟨hw0, hw'⟩
  refine ⟨HZ, HK, HKneg, hU, hW, ?_, ?_⟩
  · exact HU.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hroot.1 hA.le) (Real.sqrt_nonneg _))
      (abs_nonneg _)).trans_eq (by ring))
  · exact HW.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hroot.2 hA.le) (Real.sqrt_nonneg _))
      (abs_nonneg _)).trans_eq (by ring))

/-- The fixed long-tail exponents give powers twenty-seven and twenty-five, stronger than the common twenty-fourth power. -/
theorem exists_restartShearTail_entrance_fixed_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∃ C > (0 : ℝ),
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 128) →
        (0 < ζ ∧ ζ ≤ a ^ (550 : ℝ) ∧ ζ ≤ 2 * ε * a) →
        (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
        let Y := restartShearTailProjectiveEntry h a 50 ζ ν (shearTailTime a 90)
        let Z := fun r => entranceReturnState (Y r)
        let κ := restartShearTailEntranceRadius h a 50 90 ζ ν
        DifferentiableAt ℝ Z ρ ∧ DifferentiableAt ℝ κ ρ ∧
        0 < -deriv κ ρ ∧ 0 < Z ρ 1 ∧ 0 < Z ρ 3 ∧
        |deriv (fun r => Z r 1) ρ| ≤ C * a ^ 27 * Real.sqrt (Z ρ 1) * |deriv κ ρ| ∧
        |deriv (fun r => Z r 3) ρ| ≤ C * a ^ 25 * Real.sqrt (Z ρ 3) * |deriv κ ρ| := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearTail_entrance_weighted_cone
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨min hC (min hV 1), lt_min hhC (lt_min hhV zero_lt_one), ?_⟩
  intro h hh
  obtain ⟨A, hA, HA⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ 50 90 (by norm_num) (by norm_num)
  obtain ⟨aC, haC, HAC⟩ := HA 550 (by norm_num)
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    50 90 550 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨120 * A, by positivity, min aC aV, lt_min haC haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y Z κ
  obtain ⟨HZ, HK, HKneg, hU, hW, HU, HW⟩ :=
    HAC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨ha1, _, hT, _, _, HT, Hu, Hv, Hw⟩ :=
    HAV a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  let z := restartShearTailFlow h a 50 ζ ν (shearTailTime a 90) ρ
  have Htime := HT _ ⟨hT, le_rfl⟩
  have Hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4 := Htime.2.2.2.1
  have Hclock : 0 < 1 + z 0 :=
    (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le Htime.2.2.2.2.2.2.2.2.2.1
  have Hnon : 0 ≤ Y ρ 1 ∧ 0 ≤ Y ρ 2 ∧ 0 ≤ Y ρ 3 :=
    ⟨div_nonneg (mul_nonneg (Real.sqrt_nonneg _) Hn.1) Hclock.le,
      div_nonneg (mul_nonneg (Real.sqrt_nonneg _) Hn.2.1) Hclock.le,
      div_nonneg (mul_nonneg (Real.sqrt_nonneg _) Hn.2.2) Hclock.le⟩
  have hh1 := hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hu : Y ρ 1 ≤ 20 * a ^ 48 := by
    have H : Y ρ 1 ≤ 20 * h * a ^ (48 : ℕ) := by
      simpa only [Y, restartShearTailProjectiveEntry,
        show (50 : ℝ) - 2 = 48 by norm_num, Real.rpow_ofNat] using Hu
    exact H.trans (by gcongr; linarith only [hh1])
  have hv : Y ρ 2 ≤ 40 * a ^ 8 := by
    calc
      _ ≤ 40 * ζ * a ^ (-6 * (90 : ℝ) - 2) := Hv
      _ ≤ 40 * (a ^ (550 : ℝ) * a ^ (-6 * (90 : ℝ) - 2)) := by
        have H := mul_le_mul_of_nonneg_right hζ.2.1 (Real.rpow_nonneg ha.1.le (-6 * (90 : ℝ) - 2))
        nlinarith only [H]
      _ = _ := by rw [← Real.rpow_add ha.1]; norm_num [Real.rpow_natCast]
  have hw : Y ρ 3 ≤ 80 * a ^ 44 := by
    have H : Y ρ 3 ≤ 80 * ε * a ^ (44 : ℕ) := by
      simpa only [Y, restartShearTailProjectiveEntry,
        show (90 : ℝ) / 2 - 1 = 44 by norm_num, Real.rpow_ofNat] using Hw
    exact H.trans (by gcongr; linarith only [hε.2])
  have Hroot := shear_tail_entrance_cone_powers ⟨ha.1, ha1⟩ ⟨Hnon.1, hu⟩ ⟨Hnon.2.1, hv⟩ ⟨Hnon.2.2, hw⟩
  have HrootU : (1 + |Real.log a|) * Real.sqrt (Y ρ 1 * Y ρ 2) ≤ 120 * a ^ 27 :=
    Hroot.1.trans (mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg ha.1.le 27))
  refine ⟨HZ, HK, HKneg, hU, hW, ?_, ?_⟩
  · calc
      _ ≤ A * ((1 + |Real.log a|) * Real.sqrt (Y ρ 1 * Y ρ 2)) * Real.sqrt (Z ρ 1) * |deriv κ ρ| :=
        HU.trans_eq (by ring)
      _ ≤ A * (120 * a ^ 27) * Real.sqrt (Z ρ 1) * |deriv κ ρ| := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ A * ((1 + |Real.log a|) * Real.sqrt (Y ρ 3 * Y ρ 2)) * Real.sqrt (Z ρ 3) * |deriv κ ρ| :=
        HW.trans_eq (by ring)
      _ ≤ A * (120 * a ^ 25) * Real.sqrt (Z ρ 3) * |deriv κ ρ| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hroot.2 hA.le)
            (Real.sqrt_nonneg _)) (abs_nonneg _)
      _ = _ := by ring

end BianchiIX
