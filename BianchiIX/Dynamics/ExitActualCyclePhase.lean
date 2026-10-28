import BianchiIX.Dynamics.ExitActualCycle
import BianchiIX.Algebra.ExitCyclePhase

noncomputable section

namespace BianchiIX

open Set

/-- The ordinary cyclic phase at the actual terminal endpoint has the error in D.18. -/
theorem exists_terminal_axisCycle_phase_error {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 100) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧
        |projectiveCycle (coreTailState h Y) 0 - (1 + 2 / α)| ≤ C * (b / α ^ 2 + h ^ 2 / α ^ 3) := by
  obtain ⟨A, hA, ε, hε, HE⟩ := exists_terminal_axisCycle_regular hη hJ
  refine ⟨4 * A, by linarith only [hA], ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum Y h
  have hα0 : 0 < α := hα.1
  obtain ⟨HV, HB, HF, _⟩ := HE α b u w hα hb hsmall hsum
  have ht : coreTailTime h Y ∈ Icc 0 (coreTailTime h Y) := ⟨HV.1.1.1.le, le_rfl⟩
  have H := HF _ ht
  let y := coreTailState h Y
  have hm : y 0 < 1 := H.1
  have hR : |coreRadius (y 0) (y 2) - (2 + 2 * α)| ≤ A * b := H.2.1
  have hw : |y 1| + |y 3| ≤ A * b := H.2.2.1
  have hB : A * b ≤ α / 10000 := HB.trans (div_le_div_of_nonneg_right
    ((pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ 2 * J)).trans_eq (pow_one α)) (by norm_num))
  have hv : y 2 = h := coreTailState_active HV
  have hvsmall : 0 ≤ y 2 ∧ y 2 ≤ α / 100 := by
    rw [hv]
    refine ⟨(mul_pos hη.1 (pow_pos hα.1 J)).le, ?_⟩
    have hp : α ^ J ≤ α := (pow_le_pow_of_le_one hα.1.le hα.2 hJ).trans_eq (pow_one α)
    change η * α ^ J ≤ α / 100
    nlinarith only [mul_le_mul_of_nonneg_left hp hη.1.le, mul_le_mul_of_nonneg_right hη.2 hα.1.le]
  have hsplit : 1 - exitTailGap (coreRadius (y 0) (y 2)) (y 2) = y 0 := by
    rw [exitTailGap_of_coreRadius hm]
    ring
  have hdelta : 2 - exitTailGap (coreRadius (y 0) (y 2)) (y 2) = y 0 + 1 := by linarith only [hsplit]
  have HP := exitCycle_terminal_phase_error hα hB hR hw hvsmall
  rw [hsplit, hdelta] at HP
  change |projectiveCycle y 0 - (1 + 2 / α)| ≤ 4 * (A * b / α ^ 2 + (y 2) ^ 2 / α ^ 3) at HP
  rw [hv] at HP
  refine ⟨HV, HP.trans ?_⟩
  have Hnonneg := mul_nonneg (sub_nonneg.mpr hA) (div_nonneg (sq_nonneg h) (pow_nonneg hα.1.le 3))
  simp only [mul_div_assoc]
  nlinarith only [Hnonneg]

end BianchiIX
