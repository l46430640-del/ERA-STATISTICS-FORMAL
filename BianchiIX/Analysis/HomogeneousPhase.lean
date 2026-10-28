import BianchiIX.Analysis.HomogeneousCone

noncomputable section

namespace BianchiIX

/-- A unit-phase error estimate controls the signed derivative ratio in either orientation. -/
theorem homogeneous_phase_ratio_of_unit
    (D : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) {R a b A : ℝ}
    (hunit : ∀ z : Fin 3 → ℝ, R * z 0 = 1 → |z 1| ≤ a → |z 2| ≤ b →
      |D z 0 - 1| ≤ A)
    (v : Fin 3 → ℝ) (hc : R * v 0 ≠ 0)
    (hva : |v 1| ≤ a * |R * v 0|) (hvb : |v 2| ≤ b * |R * v 0|) :
    |D v 0 / (R * v 0) - 1| ≤ A := by
  let c := R * v 0
  have hc' : c ≠ 0 := hc
  let z := c⁻¹ • v
  have hz0 : R * z 0 = 1 := by
    change R * (c⁻¹ * v 0) = 1
    calc
      _ = c⁻¹ * c := by dsimp only [c]; ring
      _ = 1 := inv_mul_cancel₀ hc
  have hz (i : Fin 3) (s : ℝ) (hi : |v i| ≤ s * |c|) : |z i| ≤ s := by
    change |c⁻¹ * v i| ≤ s
    rw [abs_mul, abs_inv]
    calc
      _ ≤ |c|⁻¹ * (s * |c|) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (abs_nonneg _))
      _ = s := by field_simp
  have H := hunit z hz0 (hz 1 a hva) (hz 2 b hvb)
  have hd : D z 0 = D v 0 / c := by
    dsimp only [z]
    rw [map_smul]
    change c⁻¹ * D v 0 = D v 0 / c
    ring
  rwa [hd] at H

end BianchiIX
