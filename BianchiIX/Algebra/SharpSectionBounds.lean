import BianchiIX.Algebra.SectionBounds

noncomputable section

namespace BianchiIX

/-- The original flux density satisfies the constants of (5.15) on the full small section. -/
theorem small_section_sharp_flux_bounds {h d b c p s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 128) (hd : 0 < d) (hdh : d < h / 8)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hbd : b ≤ d) (hcd : c ≤ d) (hs : |s| ≤ d)
    (hp : p < 0) (hconstraint : constraint p s h b c = 1) :
    h ^ 2 - 4 * h * d ≤ curvature h b c ∧ h ^ 2 / 2 < curvature h b c ∧
      1 - h ^ 2 - 2 * d ^ 2 ≤ p ^ 2 ∧
      15 / 16 < |p| ∧ |p| ≤ 1 ∧
      47 / 32 < sectionFluxDensity p s ∧ sectionFluxDensity p s < 2 := by
  have hQlo : h ^ 2 - 4 * h * d ≤ curvature h b c := by
    unfold curvature
    nlinarith [sq_nonneg (b - c), mul_nonneg hh.le (sub_nonneg.mpr hbd),
      mul_nonneg hh.le (sub_nonneg.mpr hcd)]
  have hQpos : h ^ 2 / 2 < curvature h b c := by
    nlinarith [mul_pos hh (sub_pos.mpr hdh)]
  have hQhi : curvature h b c ≤ h ^ 2 + d ^ 2 := by
    unfold curvature
    nlinarith [mul_nonneg (by linarith : 0 ≤ d - b + c) (by linarith : 0 ≤ d + b - c),
      mul_nonneg hh.le hb, mul_nonneg hh.le hc]
  have hs2 : s ^ 2 ≤ d ^ 2 := sq_le_sq.mpr (by simpa only [abs_of_pos hd] using hs)
  have hcon : p ^ 2 + s ^ 2 + curvature h b c = 1 := hconstraint
  have hp2 := (small_section_bounds hh (by linarith) hb hc (hbd.trans hdh.le)
    (hcd.trans hdh.le) (hs.trans (by linarith)) hp hconstraint).2.1
  have habs : 15 / 16 < |p| := by
    rw [abs_of_neg hp]
    nlinarith [sq_nonneg (p + 15 / 16)]
  have habs1 : |p| ≤ 1 := by
    rw [abs_of_neg hp]
    nlinarith [sq_nonneg s, sq_nonneg (p + 1), sq_nonneg h]
  have hden : 0 < 2 * |p| := by positivity
  have hS0 : |p| ^ 2 ≤ shearSq p s := by
    rw [sq_abs]
    unfold shearSq
    nlinarith [sq_nonneg s]
  have hS1 : shearSq p s < 1 := by
    change p ^ 2 + s ^ 2 < 1
    nlinarith [sq_nonneg h]
  refine ⟨hQlo, hQpos, by linarith, habs, habs1, ?_, ?_⟩
  · rw [sectionFluxDensity_eq hp]
    have H : |p| / 2 ≤ shearSq p s / (2 * |p|) :=
      (le_div_iff₀ hden).mpr (by nlinarith only [hS0])
    linarith
  · rw [sectionFluxDensity_eq hp]
    have H : shearSq p s / (2 * |p|) < 1 :=
      (div_lt_iff₀ hden).mpr (by linarith)
    linarith

end BianchiIX
