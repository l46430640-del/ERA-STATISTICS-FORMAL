import BianchiIX.Algebra.CompactConnectionRadius

noncomputable section

namespace BianchiIX

/-- The prescribed phase error leaves a positive margin from the upper entrance endpoint. -/
theorem compact_connection_perturbed_radius_range {K η r : ℝ}
    (hK : 31 / 8 ≤ K ∧ K ≤ 6) (hη : 0 < η ∧ η ≤ 1 / 8)
    (herr : |r - (Real.sqrt (K ^ 2 - η ^ 2) - 2)| ≤ η ^ 2 / 24) :
    7 / 4 ≤ r ∧ r ≤ 4 - η ^ 2 / 24 ∧ r < 4 := by
  have H := compact_connection_boundary_radius_bounds hK hη
  have hηsq := pow_le_pow_left₀ hη.1.le hη.2 2
  have hlo := (abs_le.mp herr).1
  have hhi := (abs_le.mp herr).2
  have hu : r ≤ 4 - η ^ 2 / 24 := by linarith only [H.2, hhi]
  exact ⟨by nlinarith only [H.1, hlo, hηsq], hu,
    lt_of_le_of_lt hu (by nlinarith only [sq_pos_of_pos hη.1])⟩

end BianchiIX
