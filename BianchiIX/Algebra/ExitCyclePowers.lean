import BianchiIX.Algebra.ExitCycleEndpoint

noncomputable section

namespace BianchiIX

theorem exitCycle_weighted_power {α k a c e : ℝ} {p q : ℕ}
    (hα : 0 < α) (hk : 0 ≤ k) (hkc : k ≤ c / α) (he : 0 ≤ e)
    (ha : a ≤ e * α ^ p) (hp : q ≤ p) :
    a * k ^ q ≤ e * c ^ q * α ^ (p - q) := by
  calc
    a * k ^ q ≤ (e * α ^ p) * (c / α) ^ q :=
      (mul_le_mul_of_nonneg_right ha (pow_nonneg hk q)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk hkc q) (mul_nonneg he (pow_nonneg hα.le p)))
    _ = e * c ^ q * α ^ (p - q) := by
      have hpα : α ^ p = α ^ (p - q) * α ^ q := by rw [← pow_add, Nat.sub_add_cancel hp]
      rw [hpα, div_pow]
      field_simp

theorem exitCycle_scaled_wall_power {α B δ : ℝ} {p : ℕ}
    (hα : 0 < α) (hp : 2 ≤ p) (hB : B ≤ δ * α ^ p) :
    2 * B / α ^ 2 ≤ 2 * δ * α ^ (p - 2) := by
  apply (div_le_iff₀ (sq_pos_of_pos hα)).mpr
  have hpα : α ^ p = α ^ (p - 2) * α ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hp]
  rw [hpα] at hB
  nlinarith only [hB]

/-- The power budget retains the residual exponent before giving the uniform entrance bound. -/
theorem exitCycle_entrance_power {α k a e ε : ℝ} {p q : ℕ}
    (hα : 0 < α ∧ α ≤ 1) (hk : 0 ≤ k) (hkc : k ≤ (11 / 5) / α)
    (he : 0 ≤ e) (heε : e ≤ ε / (4 * (11 / 5) ^ q))
    (ha : a ≤ 2 * e * α ^ (p - 2)) (hp : q + 2 ≤ p) :
    a * k ^ q ≤ 2 * e * (11 / 5) ^ q * α ^ (p - q - 2) ∧ a * k ^ q ≤ ε / 2 := by
  have H := exitCycle_weighted_power hα.1 hk hkc (mul_nonneg (by norm_num) he) ha (by omega : q ≤ p - 2)
  have hexp : p - 2 - q = p - q - 2 := by omega
  rw [hexp] at H
  refine ⟨H, H.trans ?_⟩
  have hpow : α ^ (p - q - 2) ≤ 1 := pow_le_one₀ hα.1.le hα.2
  have hcoeff := (le_div_iff₀ (by positivity : 0 < 4 * (11 / 5 : ℝ) ^ q)).mp heε
  have H1 := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * e * (11 / 5 : ℝ) ^ q)
  nlinarith only [H1, hcoeff]

end BianchiIX
