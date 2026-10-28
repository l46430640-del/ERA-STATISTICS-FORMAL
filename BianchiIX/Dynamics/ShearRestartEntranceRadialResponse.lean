import BianchiIX.Dynamics.EntrancePhysicalRadialResponse
import BianchiIX.Dynamics.ShearRestartEntranceDifferentialInputs
import BianchiIX.Dynamics.ShearRestartCoreResponse
import BianchiIX.Dynamics.EntrancePartialCoreEntry

noncomputable section

namespace BianchiIX

open Set

/-- The exact shear family's physical radius stays decreasing through the preceding entrance. -/
theorem exists_restartShearEntrance_radial_response :
    ∃ hstar > (0 : ℝ), ∃ B > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let κ := fun t => coreRadius (entranceReturnState (Y t) 0) (entranceReturnState (Y t) 2)
            Y ρ 2 < 1 →
            DifferentiableAt ℝ κ ρ ∧ 6 ≤ κ ρ ∧ 1 / (32 * a) ≤ κ ρ ∧ κ ρ ≤ 64 / a ∧
            |κ ρ - k ρ| ≤ B * a ∧ |deriv κ ρ - deriv k ρ| ≤ B / a ∧
            1 / (8192 * a ^ 2) ≤ -deriv κ ρ ∧ -deriv κ ρ ≤ 1537 / a ^ 2 := by
  obtain ⟨C, hC, δ, hδ, hδsmall, HC⟩ := exists_entrance_physical_curve_bounds
  obtain ⟨hI, hhI, D, hD, HI⟩ := exists_restartShearEntrance_differential_inputs
  obtain ⟨hG, hhG, _, _, HG⟩ := exists_restartFastShearCore_response
  let B := 48 * C + 96 * C * D + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBC : 48 * C ≤ B := by dsimp only [B]; linarith only [mul_pos hC hD]
  have hBCD : 96 * C * D ≤ B := by dsimp only [B]; linarith only [hC]
  refine ⟨min hI hG, lt_min hhI hhG, B, hB, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aI, haI, HaI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aG, haG, HaG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P
    (by linarith only [hq]) (by linarith only [hP])
  refine ⟨min aI (min aG (1 / (8192 * B))), lt_min haI (lt_min haG (by positivity)), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k κ hv
  have ha' := ha.2.trans (min_le_right _ _)
  have haB : a ≤ 1 / (8192 * B) := ha'.trans (min_le_right _ _)
  obtain ⟨HY, hk8, hklo, hkhi, hm, huδ, hv', hwδ, hsum, Hd0, HDwall'⟩ :=
    HaI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, _, _, Hklo, Hkhi, _⟩ := HaG a ⟨ha.1, ha'.trans (min_le_left _ _)⟩
    ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  change 8 ≤ k ρ at hk8
  change 1 / (16 * a) ≤ k ρ at hklo
  change k ρ ≤ 32 / a at hkhi
  change Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ δ / (2 * k ρ) at hsum
  change 1 / (4096 * a ^ 2) ≤ -deriv k ρ at Hklo
  change -deriv k ρ ≤ 1536 / a ^ 2 at Hkhi
  have hkpos : 0 < k ρ := by linarith only [hk8]
  have hu : 0 < Y ρ 1 ∧ Y ρ 1 ≤ 1 / 10000 := ⟨huδ.1, huδ.2.trans hδsmall⟩
  have hw : 0 ≤ Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000 := ⟨hwδ.1.le, hwδ.2.trans hδsmall⟩
  have hk' : 7 / 4 ≤ coreRadius (Y ρ 0) (Y ρ 2) := by change 7 / 4 ≤ k ρ; linarith only [hk8]
  obtain ⟨Hκ, _, Hval, Hder⟩ := HC Y ρ D HY hD.le hk' hm.le huδ hv' hwδ Hd0 HDwall'
  let b := Y ρ 1 + Y ρ 3
  let H := Y ρ 1 * Y ρ 2 + (Y ρ 2) ^ 2 * b ^ 2
  change |κ ρ - k ρ| ≤ C * (b ^ 2 + H) / k ρ at Hval
  change |deriv κ ρ - deriv k ρ| ≤ C * D * (b ^ 2 + k ρ * H) at Hder
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity [hu.1, hv'.1]
  have hb0 : 0 ≤ b := add_nonneg hu.1.le hw.1
  have hb1 : b ≤ 1 := by dsimp only [b]; linarith only [hu.2, hw.2]
  have hb2 : b ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hb0 hb1 2
  have hV2 : (Y ρ 2) ^ 2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ hv'.1.le hv'.2.le 2
  have hUV : Y ρ 1 * Y ρ 2 ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul (hu.2.trans (by norm_num)) hv'.2.le hv'.1.le (by norm_num)
      _ = _ := one_mul 1
  have hH : H ≤ 2 := by
    have Hprod : (Y ρ 2) ^ 2 * b ^ 2 ≤ 1 := by
      calc
        _ ≤ (1 : ℝ) * 1 := mul_le_mul hV2 hb2 (sq_nonneg _) (by norm_num)
        _ = _ := one_mul 1
    dsimp only [H]
    linarith only [hUV, Hprod]
  have Hvalue : |κ ρ - k ρ| ≤ B * a := Hval.trans (by
    calc
      _ ≤ C * (1 + 2) / k ρ := by gcongr
      _ ≤ C * (1 + 2) / (1 / (16 * a)) := div_le_div_of_nonneg_left (by positivity) (by positivity [ha.1]) hklo
      _ = (48 * C) * a := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBC ha.1.le)
  have Hderiv : |deriv κ ρ - deriv k ρ| ≤ B / a := Hder.trans (by
    calc
      _ ≤ C * D * (1 + k ρ * 2) := by gcongr
      _ ≤ C * D * (3 * k ρ) := by gcongr; linarith only [hk8]
      _ ≤ C * D * (3 * (32 / a)) := by gcongr
      _ = (96 * C * D) / a := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hBCD ha.1.le)
  have Hsmall : B / a ≤ 1 / (8192 * a ^ 2) := by
    have H := (le_div_iff₀ (by positivity : 0 < 8192 * B)).mp haB
    apply (div_le_div_iff₀ ha.1 (by positivity [ha.1] : 0 < 8192 * a ^ 2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_right H ha.1.le]
  have Habs := abs_le.mp (Hderiv.trans Hsmall)
  obtain ⟨hκ6, hκ, _⟩ := entranceReturn_partialCore_entry hk8 hm.le ⟨hu.1.le, hu.2⟩ hv' hw
    ⟨hδ, hδsmall⟩ hsum
  change 99 / 100 * k ρ ≤ κ ρ ∧ κ ρ ≤ 101 / 100 * k ρ at hκ
  have Hκlo : 1 / (32 * a) ≤ κ ρ := by
    calc
      _ = (1 / 2) * (1 / (16 * a)) := by ring
      _ ≤ (1 / 2) * k ρ := mul_le_mul_of_nonneg_left hklo (by norm_num)
      _ ≤ _ := by linarith only [hκ.1, hkpos]
  have Hκhi : κ ρ ≤ 64 / a := by
    calc
      _ ≤ 2 * k ρ := by linarith only [hκ.2, hkpos]
      _ ≤ 2 * (32 / a) := mul_le_mul_of_nonneg_left hkhi (by norm_num)
      _ = _ := by ring
  refine ⟨Hκ, hκ6, Hκlo, Hκhi, Hvalue, Hderiv, ?_, ?_⟩
  · have heq : 1 / (4096 * a ^ 2) = 2 * (1 / (8192 * a ^ 2)) := by ring
    rw [heq] at Hklo
    linarith only [Habs.2, Hklo]
  · have Hunit : 1 / (8192 * a ^ 2) ≤ 1 / a ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1]) (by nlinarith only [sq_nonneg a])
    have heq : 1536 / a ^ 2 + 1 / a ^ 2 = 1537 / a ^ 2 := by ring
    linarith only [Habs.1, Hkhi, Hunit, heq]

end BianchiIX
