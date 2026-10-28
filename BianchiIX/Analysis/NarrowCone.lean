import BianchiIX.Analysis.HomogeneousCone
import Mathlib.Tactic.Linarith

noncomputable section

namespace BianchiIX

/-- A narrow unit-phase cone is a convex interpolation of the radial direction
and the full unit-phase cone. -/
theorem linear_narrow_cone_bound (A : (Fin 3 → ℝ) →L[ℝ] ℝ) (r v : Fin 3 → ℝ)
    {a b C E θ : ℝ} (hr1 : r 1 = 0) (hr2 : r 2 = 0) (hv0 : v 0 = r 0)
    (hθ : 0 ≤ θ ∧ θ ≤ 1) (hv1 : |v 1| ≤ θ * a) (hv2 : |v 2| ≤ θ * b)
    (hunit : ∀ z : Fin 3 → ℝ, z 0 = r 0 → |z 1| ≤ a → |z 2| ≤ b → |A z| ≤ C)
    (hrad : |A r| ≤ E) : |A v| ≤ θ * C + E := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hrad
  by_cases hθ0 : θ = 0
  · have hv : v = r := by
      ext i
      fin_cases i
      · exact hv0
      · change v 1 = r 1
        rw [hr1]
        simpa only [hθ0, zero_mul, abs_nonpos_iff] using hv1
      · change v 2 = r 2
        rw [hr2]
        simpa only [hθ0, zero_mul, abs_nonpos_iff] using hv2
    simpa only [hθ0, zero_mul, zero_add, hv] using hrad
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθ0)
    let z := r + θ⁻¹ • (v - r)
    have hz0 : z 0 = r 0 := by simp [z, hv0]
    have hz (i : Fin 3) (s : ℝ) (hri : r i = 0) (hi : |v i| ≤ θ * s) : |z i| ≤ s := by
      have hzi : z i = θ⁻¹ * v i := by simp [z, hri]
      rw [hzi, abs_mul, abs_inv, abs_of_pos hθpos]
      calc
        _ ≤ θ⁻¹ * (θ * s) := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hθ.1)
        _ = s := by field_simp
    have Hz := hunit z hz0 (hz 1 a hr1 hv1) (hz 2 b hr2 hv2)
    have hv : v = θ • z + (1 - θ) • r := by
      ext i
      change v i = θ * (r i + θ⁻¹ * (v i - r i)) + (1 - θ) * r i
      field_simp
      ring
    calc
      |A v| = |θ * A z + (1 - θ) * A r| := by rw [hv, map_add, map_smul, map_smul]; rfl
      _ ≤ θ * |A z| + (1 - θ) * |A r| := by
        simpa only [abs_mul, abs_of_nonneg hθ.1, abs_of_nonneg (sub_nonneg.mpr hθ.2)] using
          abs_add_le (θ * A z) ((1 - θ) * A r)
      _ ≤ θ * C + (1 - θ) * E := add_le_add
        (mul_le_mul_of_nonneg_left Hz hθ.1) (mul_le_mul_of_nonneg_left hrad (sub_nonneg.mpr hθ.2))
      _ ≤ θ * C + E := by nlinarith only [hθ.1, hE]

end BianchiIX
