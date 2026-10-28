import BianchiIX.Analysis.RestartConeBudget

noncomputable section

namespace BianchiIX

/-- The fast-entry amplitudes are uniformly of radial order on the positive weak-wall family. -/
theorem restart_entry_linear_amplitude_budget {r h M q P ζ U W : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hh : 0 ≤ h) (hM : 0 ≤ M) (hq : 3 < q) (hP : 4 < P)
    (hζ : 0 ≤ ζ ∧ ζ ≤ r ^ P)
    (hU : 0 ≤ U ∧ U ≤ 32 * h * r ^ (q - 2))
    (hW : 0 ≤ W ∧ W ≤ 2048 * M * ζ / r ^ 3) :
    U ≤ 32 * h * r ∧ W ≤ 2048 * M * r ∧ U + W ≤ (32 * h + 2048 * M) * r := by
  have hr0 := hr.1
  have hp1 : r ^ (q - 2) ≤ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2
      (by linarith only [hq] : (1 : ℝ) ≤ q - 2)
  have hp4 : ζ ≤ r ^ 4 := hζ.2.trans (by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2
      (by linarith only [hP] : (4 : ℝ) ≤ P))
  have HU : U ≤ 32 * h * r := hU.2.trans (mul_le_mul_of_nonneg_left hp1 (by positivity))
  have HW : W ≤ 2048 * M * r := hW.2.trans (calc
    _ ≤ 2048 * M * r ^ 4 / r ^ 3 := by gcongr
    _ = _ := by field_simp)
  exact ⟨HU, HW, (add_le_add HU HW).trans_eq (by ring)⟩

end BianchiIX
