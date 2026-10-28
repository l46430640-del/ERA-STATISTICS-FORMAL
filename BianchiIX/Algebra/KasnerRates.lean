import BianchiIX.Algebra.Flow

noncomputable section

namespace BianchiIX

theorem kasner_rate_sum_product {p s : ℝ} (h : shearSq p s = 1) :
    rateOne p s + rateTwo p s + rateThree p s = -3 ∧
      rateOne p s * rateTwo p s * rateThree p s = 2 * (2 * p - 1) ^ 2 * (p + 1) := by
  have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcircle : p ^ 2 + s ^ 2 = 1 := h
  dsimp only [rateOne, rateTwo, rateThree]
  rw [h]
  constructor
  · ring
  · calc
      (-1 + 2 * p) * (-1 - p + Real.sqrt 3 * s) * (-1 - p - Real.sqrt 3 * s) =
          (2 * p - 1) * ((1 + p) ^ 2 - 3 * s ^ 2) := by
            ring_nf
            rw [hsqrt]
            ring
      _ = (2 * p - 1) * (2 * (2 * p - 1) * (p + 1)) := by
        congr 1
        nlinarith only [hcircle]
      _ = 2 * (2 * p - 1) ^ 2 * (p + 1) := by ring

/-- Off the three Taub points, exactly one wall grows and the other two decay on the Kasner circle. -/
theorem kasner_growth_signs {p s : ℝ} (h : shearSq p s = 1)
    (hp : p ≠ -1) (hp' : p ≠ 1 / 2) :
    (0 < rateOne p s ∧ rateTwo p s < 0 ∧ rateThree p s < 0) ∨
      (rateOne p s < 0 ∧ 0 < rateTwo p s ∧ rateThree p s < 0) ∨
      (rateOne p s < 0 ∧ rateTwo p s < 0 ∧ 0 < rateThree p s) := by
  obtain ⟨hsum, hprod⟩ := kasner_rate_sum_product h
  have hcircle : p ^ 2 + s ^ 2 = 1 := h
  have hlo : -1 < p := lt_of_le_of_ne (by nlinarith only [hcircle, sq_nonneg s]) (Ne.symm hp)
  have hsq : 0 < (2 * p - 1) ^ 2 := sq_pos_of_ne_zero (by intro heq; apply hp'; linarith only [heq])
  have hpositive : 0 < rateOne p s * rateTwo p s * rateThree p s := by
    rw [hprod]
    exact mul_pos (mul_pos (by norm_num) hsq) (by linarith only [hlo])
  rcases mul_pos_iff.mp hpositive with ⟨hab, hc⟩ | ⟨hab, hc⟩
  · rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · linarith only [hsum, ha, hb, hc]
    · exact Or.inr (Or.inr ⟨ha, hb, hc⟩)
  · rcases mul_neg_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl ⟨ha, hb, hc⟩
    · exact Or.inr (Or.inl ⟨ha, hb, hc⟩)

end BianchiIX
