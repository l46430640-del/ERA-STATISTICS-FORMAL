import BianchiIX.Dynamics.CoreTailHeightOrder
import BianchiIX.Dynamics.ExitActualCycle

noncomputable section

namespace BianchiIX

open Set

/-- One lowest tail supplies the old-coordinate geometry for every higher auxiliary endpoint. -/
theorem exists_terminal_tail_geometry_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let y := coreTailState h Y
      coreTailValid h Y ∧ y 0 < 1 ∧
        |coreRadius (y 0) (y 2) - (2 + 2 * α)| ≤ A * b ∧
        |y 1| + |y 3| ≤ A * b ∧ A * b ≤ α / 10000 ∧
        (0 ≤ y 2 ∧ y 2 ≤ α / 100) ∧ 39 / 10 * α ^ 2 ≤ projectiveCycleDenom y := by
  obtain ⟨A, hA, ε, hε, HE⟩ := exists_terminal_axisCycle_regular hη₀ hJ
  refine ⟨A, hA, ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h y
  have hη : 0 < η := hη₀.1.trans_le hηlo
  obtain ⟨HV₀, HB, HF, _⟩ := HE α b u w hα hb hsmall hsum
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.le
    dsimp only [h]
    nlinarith only [H, hηhi]
  obtain ⟨HV, htime⟩ := coreTailValid_of_height_le HV₀
    (mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)) hh1
  change coreTailValid h Y at HV
  have H := HF (coreTailTime h Y) ⟨HV.1.1.1.le, htime⟩
  have HB' : A * b ≤ α / 10000 := HB.trans (div_le_div_of_nonneg_right
    ((pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ 2 * J)).trans_eq (pow_one α)) (by norm_num))
  have hv : 0 ≤ y 2 ∧ y 2 ≤ α / 100 := by
    change 0 ≤ coreTailState h Y 2 ∧ coreTailState h Y 2 ≤ _
    rw [coreTailState_active HV]
    refine ⟨mul_nonneg hη.le (pow_nonneg hα.1.le J), ?_⟩
    have hp := (pow_le_pow_of_le_one hα.1.le hα.2 hJ).trans_eq (pow_one α)
    change η * α ^ J ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hp hη.le, mul_le_mul_of_nonneg_right hηhi hα.1.le]
  refine ⟨HV, H.1, H.2.1, H.2.2.1, HB', hv, ?_⟩
  have HH : 39 / 10 * α ^ 2 + 2 / 5 * (y 2) ^ 2 < projectiveCycleDenom y := H.2.2.2.1
  nlinarith only [HH, sq_nonneg (y 2)]

end BianchiIX
