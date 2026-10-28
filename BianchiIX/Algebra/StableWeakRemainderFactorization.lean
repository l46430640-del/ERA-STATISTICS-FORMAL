import BianchiIX.Algebra.StableWeakRemainderDerivatives

noncomputable section

namespace BianchiIX

def stableWeakSecondKernel (m w : ℝ) : ℝ :=
  (stableWeakRadius m w ^ 2 + stableWeakRadius m w * (m + 1) + (m + 1) ^ 2) /
    (stableWeakRadius m w ^ 3 * (stableWeakRadius m w + (m + 1)))

theorem stableWeakRemainder_factorization {m w : ℝ} (hm : -1 < m) :
    stableWeakRemainder m w = -w ^ 4 / (2 * (m + 1) * (stableWeakRadius m w + (m + 1)) ^ 2) :=
  stableWeakRadius_quartic_defect hm

theorem stableWeakRemainder_gradient_factorization {m w : ℝ} (hm : -1 < m) :
    stableWeakRemainderM m w =
      w ^ 4 * (stableWeakRadius m w + 2 * (m + 1)) /
        (2 * (m + 1) ^ 2 * stableWeakRadius m w * (stableWeakRadius m w + (m + 1)) ^ 2) ∧
      stableWeakRemainderW m w = -w ^ 3 / ((m + 1) * stableWeakRadius m w * (stableWeakRadius m w + (m + 1))) := by
  have hL : m + 1 ≠ 0 := by linarith
  have hS := ne_of_gt (stableWeakRadius_pos (w := w) hm)
  have hsum : stableWeakRadius m w + (m + 1) ≠ 0 := by
    have H := stableWeakRadius_pos (w := w) hm
    linarith
  have hw : w ^ 2 = stableWeakRadius m w ^ 2 - (m + 1) ^ 2 := by
    nlinarith only [stableWeakRadius_sq m w]
  constructor
  · unfold stableWeakRemainderM
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw]
    field_simp
    ring
  · unfold stableWeakRemainderW
    rw [show w ^ 3 = w * w ^ 2 by ring, hw]
    field_simp
    ring

theorem stableWeakRemainder_hessian_factorization {m w : ℝ} (hm : -1 < m) :
    stableWeakRemainderMM m w = -(w ^ 4 / (m + 1) ^ 3) * stableWeakSecondKernel m w ∧
      stableWeakRemainderMW m w = w ^ 3 / (m + 1) ^ 2 * stableWeakSecondKernel m w ∧
      stableWeakRemainderWW m w = -(w ^ 2 / (m + 1)) * stableWeakSecondKernel m w := by
  have hL : m + 1 ≠ 0 := by linarith
  have hS := ne_of_gt (stableWeakRadius_pos (w := w) hm)
  have hsum : stableWeakRadius m w + (m + 1) ≠ 0 := by
    have H := stableWeakRadius_pos (w := w) hm
    linarith
  have hw : w ^ 2 = stableWeakRadius m w ^ 2 - (m + 1) ^ 2 := by
    nlinarith only [stableWeakRadius_sq m w]
  refine ⟨?_, ?_, ?_⟩
  · unfold stableWeakRemainderMM stableWeakSecondKernel
    rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw]
    field_simp
    ring
  · unfold stableWeakRemainderMW stableWeakSecondKernel
    rw [show w ^ 3 = w * w ^ 2 by ring, hw]
    field_simp
    ring
  · unfold stableWeakRemainderWW stableWeakSecondKernel
    rw [hw]
    field_simp
    ring

theorem stableWeakSecondKernel_bounds {m w : ℝ} (hm : -1 < m) :
    0 ≤ stableWeakSecondKernel m w ∧ stableWeakSecondKernel m w ≤ 3 / (m + 1) ^ 2 := by
  have hL : 0 < m + 1 := by linarith
  have hS := stableWeakRadius_pos (w := w) hm
  have hLS : m + 1 ≤ stableWeakRadius m w := phaseNorm_ge hL.le
  have hsum : 0 < stableWeakRadius m w + (m + 1) := by positivity
  have hnum : stableWeakRadius m w ^ 2 + stableWeakRadius m w * (m + 1) + (m + 1) ^ 2 ≤
      3 * stableWeakRadius m w ^ 2 := by
    have H1 := mul_le_mul_of_nonneg_left hLS hS.le
    have H2 := pow_le_pow_left₀ hL.le hLS 2
    nlinarith only [H1, H2]
  have hden : (m + 1) ^ 2 ≤ stableWeakRadius m w * (stableWeakRadius m w + (m + 1)) := by
    have H := mul_le_mul hLS (show m + 1 ≤ stableWeakRadius m w + (m + 1) by linarith) hL.le hS.le
    nlinarith only [H]
  refine ⟨by unfold stableWeakSecondKernel; positivity, ?_⟩
  calc
    _ ≤ 3 * stableWeakRadius m w ^ 2 /
        (stableWeakRadius m w ^ 3 * (stableWeakRadius m w + (m + 1))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 3 / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1))) := by field_simp
    _ ≤ 3 / (m + 1) ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

end BianchiIX
