import BianchiIX.Algebra.MatchingPhase

noncomputable section

namespace BianchiIX

/-- The reflected boundary radius lies in the precise overlap interval used in B.46. -/
theorem compact_connection_boundary_radius_bounds {K η : ℝ}
    (hK : 31 / 8 ≤ K ∧ K ≤ 6) (hη : 0 < η ∧ η ≤ 1 / 8) :
    15 / 8 - 8 * η ^ 2 / 31 ≤ Real.sqrt (K ^ 2 - η ^ 2) - 2 ∧
      Real.sqrt (K ^ 2 - η ^ 2) - 2 ≤ 4 - η ^ 2 / 12 := by
  have hK0 : 0 < K := by linarith only [hK.1]
  have hrad : 0 ≤ K ^ 2 - η ^ 2 := by nlinarith only [hK.1, hη.1, hη.2]
  let s := Real.sqrt (K ^ 2 - η ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = K ^ 2 - η ^ 2 := Real.sq_sqrt hrad
  have hsK : s ≤ K := by nlinarith only [hsq, hK0, sq_nonneg η]
  have hdiv : η ^ 2 / K ≤ 8 * η ^ 2 / 31 := by
    have H := div_le_div_of_nonneg_left (sq_nonneg η) (by norm_num : (0 : ℝ) < 31 / 8) hK.1
    convert! H using 1
    ring
  have hden : η ^ 2 / K * K = η ^ 2 := div_mul_cancel₀ _ hK0.ne'
  have hlower : K - η ^ 2 / K ≤ s := by
    have H := mul_nonneg hs0 (sub_nonneg.mpr hsK)
    nlinarith only [hsq, hden, H, hK0]
  have hu : η ^ 2 / (2 * K) ≤ K - s := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * K)).mpr
    nlinarith only [hsq, sq_nonneg (K - s)]
  have hu' : η ^ 2 / 12 ≤ η ^ 2 / (2 * K) :=
    div_le_div_of_nonneg_left (sq_nonneg η) (by positivity) (by linarith only [hK.2])
  exact ⟨by linarith only [hlower, hdiv, hK.1], by linarith only [hu, hu', hK.2]⟩

end BianchiIX
