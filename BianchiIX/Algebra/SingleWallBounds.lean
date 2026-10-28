import BianchiIX.Algebra.Flow

noncomputable section

namespace BianchiIX

/-- Small pairwise wall products bound the entire constrained state. -/
theorem constraint_small_wall_products {p s n b c Δ : ℝ}
    (hc : constraint p s n b c = 1)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hbc : 4 * b * c ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2)
    (hΔ : 0 ≤ Δ ∧ Δ ≤ 1 / 4) :
    p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 1 + 3 / 2 * Δ ^ 2 ∧
      p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 35 / 32 ∧ |p| < 17 / 16 := by
  have hsum : p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 1 + 3 / 2 * Δ ^ 2 := by
    dsimp [constraint, shearSq, curvature] at hc
    nlinarith only [hc, hnb, hbc, hcn]
  have hΔsq : Δ ^ 2 ≤ 1 / 16 := by nlinarith only [hΔ.1, hΔ.2]
  have hsum' : p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 35 / 32 := by
    linarith only [hsum, hΔsq]
  have hpsq : p ^ 2 < (17 / 16 : ℝ) ^ 2 := by
    nlinarith only [hsum', sq_nonneg s, sq_nonneg n, sq_nonneg b, sq_nonneg c]
  refine ⟨hsum, hsum', abs_lt.mpr ⟨?_, ?_⟩⟩ <;> nlinarith only [hpsq]

/-- A wall above the fixed height forces the other two walls below a much smaller height. -/
theorem weak_wall_sum_of_products {n b c Δ ν : ℝ}
    (hν : 0 < ν) (hn : ν ≤ n) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2) :
    b + c ≤ Δ ^ 2 / (2 * n) ∧ b + c ≤ ν / 128 := by
  have hnpos : 0 < n := hν.trans_le hn
  have hsum : 2 * n * (b + c) ≤ Δ ^ 2 := by nlinarith only [hnb, hcn]
  have hΔsq : Δ ^ 2 ≤ ν ^ 2 / 64 := by nlinarith only [hΔ.1, hΔ.2, hν]
  have hνsum := mul_le_mul_of_nonneg_right hn (add_nonneg hb hc)
  refine ⟨(le_div_iff₀ (by positivity : 0 < 2 * n)).mpr (by nlinarith only [hsum]), ?_⟩
  nlinarith only [hsum, hΔsq, hνsum, hν]

/-- The exact shear decreases uniformly while a single wall dominates. -/
theorem shearPlus_single_wall_descent {p n b c : ℝ}
    (hp : |p| ≤ 17 / 16) (hn : 0 ≤ n) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hweak : b + c ≤ n / 16) : shearPlus p n b c ≤ -(n ^ 2) / 2 := by
  obtain ⟨hplo, hphi⟩ := abs_le.mp hp
  have hmain := mul_le_mul_of_nonneg_right hphi (sq_nonneg n)
  have hcross := mul_le_mul_of_nonneg_right (show 1 - 2 * p ≤ 4 by linarith only [hplo])
    (mul_nonneg hn (add_nonneg hb hc))
  have hdiff : (b - c) ^ 2 ≤ (b + c) ^ 2 := by nlinarith only [mul_nonneg hb hc]
  have hmiddle := (mul_le_mul_of_nonneg_right (show 1 + p ≤ 3 by linarith only [hphi])
    (sq_nonneg (b - c))).trans (mul_le_mul_of_nonneg_left hdiff (by norm_num : (0 : ℝ) ≤ 3))
  have hweakSq : (b + c) ^ 2 ≤ n ^ 2 / 256 := by
    nlinarith only [hweak, hb, hc, hn]
  have hweakProd := mul_le_mul_of_nonneg_left hweak hn
  have heq : shearPlus p n b c =
      (p - 2) * n ^ 2 + (1 + p) * (b - c) ^ 2 + (1 - 2 * p) * n * (b + c) := by
    dsimp [shearPlus, curvature]
    ring
  rw [heq]
  nlinarith only [hmain, hcross, hmiddle, hweakSq, hweakProd, sq_nonneg n]

end BianchiIX
