import BianchiIX.Analysis.MatchingPhaseWeighted

noncomputable section

namespace BianchiIX

def phaseNormKernelDa (a b : ℝ) : ℝ := -1 / phaseNorm a b ^ 3

def phaseNormKernelDb (a b : ℝ) : ℝ :=
  -b * (2 * phaseNorm a b + a) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2)

theorem hasDerivAt_phaseNorm {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ha0 : 0 < a t) :
    HasDerivAt (fun s => phaseNorm (a s) (b s))
      ((a t * a' + b t * b') / phaseNorm (a t) (b t)) t := by
  have hpos : a t ^ 2 + b t ^ 2 ≠ 0 := by positivity
  convert! ((ha.pow 2).add (hb.pow 2)).sqrt hpos using 1
  dsimp [phaseNorm]
  ring

theorem hasDerivAt_phaseNormKernel {a b : ℝ → ℝ} {a' b' t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (ha0 : 0 < a t) :
    HasDerivAt (fun s => phaseNormKernel (a s) (b s))
      (phaseNormKernelDa (a t) (b t) * a' + phaseNormKernelDb (a t) (b t) * b') t := by
  have hK := phaseNorm_pos (b := b t) ha0
  have hS : 0 < phaseNorm (a t) (b t) + a t := add_pos hK ha0
  have hN := hasDerivAt_phaseNorm ha hb ha0
  have H := (hN.mul (hN.add ha)).inv (ne_of_gt (mul_pos hK hS))
  simp only [phaseNormKernel, one_div]
  apply H.congr_deriv
  dsimp [phaseNormKernelDa, phaseNormKernelDb]
  field_simp
  ring

/-- Uniform estimates use a lower bound for the positive first argument, with no lower wall bound. -/
theorem phaseNormKernel_derivative_bounds {l a b : ℝ} (hl : 0 < l) (ha : l ≤ a) :
    0 ≤ phaseNormKernel a b ∧ phaseNormKernel a b ≤ 1 / (2 * l ^ 2) ∧
      |phaseNormKernelDa a b| ≤ 1 / l ^ 3 ∧
      |b * phaseNormKernelDb a b| ≤ 3 * b ^ 2 / (4 * l ^ 4) := by
  have ha0 : 0 < a := hl.trans_le ha
  have hK := phaseNorm_pos (b := b) ha0
  have hKa := phaseNorm_ge (b := b) ha0.le
  have hKl := ha.trans hKa
  have hSl : 2 * l ≤ phaseNorm a b + a := by linarith only [ha, hKl]
  have hS : 0 < phaseNorm a b + a := add_pos hK ha0
  have hprod : 2 * l ^ 2 ≤ phaseNorm a b * (phaseNorm a b + a) := by
    have H := mul_le_mul hKl hSl (by positivity : 0 ≤ 2 * l) hK.le
    nlinarith only [H]
  have hprod2 : 4 * l ^ 4 ≤ phaseNorm a b ^ 2 * (phaseNorm a b + a) ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * l ^ 2) hprod 2
    nlinarith only [H]
  refine ⟨by unfold phaseNormKernel; positivity, ?_, ?_, ?_⟩
  · exact one_div_le_one_div_of_le (by positivity) hprod
  · rw [phaseNormKernelDa, abs_div, abs_neg, abs_one, abs_of_pos (pow_pos hK 3)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hl.le hKl 3)
  · have hid : |b * phaseNormKernelDb a b| =
        b ^ 2 * (2 * phaseNorm a b + a) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2) := by
      have H : b * phaseNormKernelDb a b =
          -(b ^ 2 * (2 * phaseNorm a b + a) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2)) := by
        dsimp [phaseNormKernelDb]
        ring
      rw [H, abs_neg, abs_of_nonneg (by positivity)]
    rw [hid]
    calc
      _ ≤ (b ^ 2 * (3 * phaseNorm a b)) / (phaseNorm a b ^ 3 * (phaseNorm a b + a) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by linarith only [hKa]) (sq_nonneg b)
      _ = 3 * b ^ 2 / (phaseNorm a b ^ 2 * (phaseNorm a b + a) ^ 2) := by field_simp
      _ ≤ 3 * b ^ 2 / (4 * l ^ 4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hprod2

end BianchiIX
