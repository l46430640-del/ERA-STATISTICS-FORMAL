import BianchiIX.Algebra.Flux

noncomputable section

namespace BianchiIX

theorem curvature_abs_le_sum_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |curvature a b c| ≤ (a + b + c) ^ 2 := by
  rw [abs_le]
  constructor
  · unfold curvature
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · unfold curvature
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

theorem wallAmplitude_le_square {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hba : b ≤ a) (hca : c ≤ a) : wallAmplitude a b c ≤ a ^ 2 := by
  have hp : a * b * c ≤ a ^ 3 := by
    calc
      a * b * c ≤ a * a * a :=
        mul_le_mul (mul_le_mul_of_nonneg_left hba ha) hca hc (mul_nonneg ha ha)
      _ = a ^ 3 := by ring
  unfold wallAmplitude
  calc
    _ ≤ (a ^ 3) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (mul_nonneg (mul_nonneg ha hb) hc) hp (by norm_num)
    _ = a ^ 2 := by rw [← Real.rpow_natCast_mul ha]; norm_num

/-- Uniform estimates on the relative closure of the negative small section. -/
theorem small_section_bounds {h b c p s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hb1 : b ≤ h / 8) (hc1 : c ≤ h / 8) (hs : |s| ≤ 1 / 8)
    (hp : p < 0) (hconstraint : constraint p s h b c = 1) :
    curvature h b c ≤ (25 / 16) * h ^ 2 ∧
      (983 / 1024 : ℝ) ≤ p ^ 2 ∧ p ≤ -15 / 16 ∧ shearSq p s ≤ 2 := by
  have hsum : h + b + c ≤ 5 / 4 * h := by linarith
  have hsum2 := pow_le_pow_left₀ (by linarith : 0 ≤ h + b + c) hsum 2
  have hcurv := abs_le.mp (curvature_abs_le_sum_sq hh.le hb hc)
  have hQ : curvature h b c ≤ (25 / 16) * h ^ 2 := by nlinarith
  have hQlo : -(25 / 16) * h ^ 2 ≤ curvature h b c := by nlinarith
  have hh2 : h ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hh.le hh1 2
  have hs2 : s ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hs)
  have hcon : p ^ 2 + s ^ 2 + curvature h b c = 1 := hconstraint
  have hp2 : (983 / 1024 : ℝ) ≤ p ^ 2 := by nlinarith
  refine ⟨hQ, hp2, ?_, ?_⟩
  · nlinarith [sq_nonneg (p + 15 / 16)]
  · unfold shearSq
    nlinarith

theorem small_section_transverse {h b c p s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hb1 : b ≤ h / 8) (hc1 : c ≤ h / 8) (hs : |s| ≤ 1 / 8)
    (hp : p < 0) (hconstraint : constraint p s h b c = 1) :
    rateOne p s * h ≤ -15 * h / 8 ∧ rateOne p s * h < 0 := by
  have hpbound := (small_section_bounds hh hh1 hb hc hb1 hc1 hs hp hconstraint).2.2.1
  have hr : rateOne p s ≤ -15 / 8 := by
    unfold rateOne shearSq
    nlinarith [sq_nonneg p, sq_nonneg s]
  have H : rateOne p s * h ≤ -15 * h / 8 := by
    nlinarith [mul_le_mul_of_nonneg_right hr hh.le]
  exact ⟨H, H.trans_lt (by nlinarith)⟩

def sectionFluxDensity (p s : ℝ) : ℝ := (shearSq p s - 2 * p) / (2 * |p|)

def correctedSectionFluxDensity (p s a b c : ℝ) : ℝ :=
  sectionFluxDensity p s / (1 + 4 * wallAmplitude a b c)

theorem sectionFluxDensity_eq {p s : ℝ} (hp : p < 0) :
    sectionFluxDensity p s = 1 + shearSq p s / (2 * |p|) := by
  rw [sectionFluxDensity, abs_of_neg hp]
  field_simp [ne_of_lt hp]
  ring

theorem small_section_flux_bounds {h b c p s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hb1 : b ≤ h / 8) (hc1 : c ≤ h / 8) (hs : |s| ≤ 1 / 8)
    (hp : p < 0) (hconstraint : constraint p s h b c = 1) :
    1 ≤ sectionFluxDensity p s ∧ sectionFluxDensity p s ≤ 3 := by
  obtain ⟨_, _, hpbound, hS⟩ := small_section_bounds hh hh1 hb hc hb1 hc1 hs hp hconstraint
  have habs : 15 / 16 ≤ |p| := by rw [abs_of_neg hp]; linarith
  have hden : 0 < 2 * |p| := by positivity
  have hS0 : 0 ≤ shearSq p s := add_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [sectionFluxDensity_eq hp]
  constructor
  · linarith [div_nonneg hS0 hden.le]
  · have H : shearSq p s / (2 * |p|) ≤ 2 :=
      (div_le_iff₀ hden).mpr (by linarith)
    linarith

theorem small_section_corrected_flux_bounds {h b c p s : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hb1 : b ≤ h / 8) (hc1 : c ≤ h / 8) (hs : |s| ≤ 1 / 8)
    (hp : p < 0) (hconstraint : constraint p s h b c = 1) :
    (1 / 2 : ℝ) ≤ correctedSectionFluxDensity p s h b c ∧
      correctedSectionFluxDensity p s h b c ≤ sectionFluxDensity p s ∧
      correctedSectionFluxDensity p s h b c ≤ 3 := by
  have hflux := small_section_flux_bounds hh hh1 hb hc hb1 hc1 hs hp hconstraint
  have hH0 : 0 ≤ wallAmplitude h b c := Real.rpow_nonneg (mul_nonneg (mul_nonneg hh.le hb) hc) _
  have hH : wallAmplitude h b c ≤ h ^ 2 := wallAmplitude_le_square hh.le hb hc (by linarith) (by linarith)
  have hh2 := pow_le_pow_left₀ hh.le hh1 2
  have hden : 0 < 1 + 4 * wallAmplitude h b c := by positivity
  have hlow : (1 / 2 : ℝ) ≤ correctedSectionFluxDensity p s h b c := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hup : correctedSectionFluxDensity p s h b c ≤ sectionFluxDensity p s := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ sectionFluxDensity p s) hH0]
  exact ⟨hlow, hup, hup.trans hflux.2⟩

end BianchiIX
