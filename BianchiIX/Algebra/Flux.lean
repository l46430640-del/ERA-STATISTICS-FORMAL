import BianchiIX.Algebra.Flow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

/-! The sharp curvature bound and the positive corrected divergence, Section 5.2. -/

namespace BianchiIX

noncomputable section

private theorem ordered_arithmetic_geometric
    {a b c r : ℝ} (hc : 0 ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (hr : r ^ 3 = a * b * c) : 3 * r ≤ a + b + c := by
  have hid : (a + b + c) ^ 3 - 27 * (a * b * c) =
      9 * c * ((a - b) ^ 2 + (a - b) * (b - c) + (b - c) ^ 2) +
        (a + b - 2 * c) ^ 3 := by ring
  have hnonneg : 0 ≤
      9 * c * ((a - b) ^ 2 + (a - b) * (b - c) + (b - c) ^ 2) +
        (a + b - 2 * c) ^ 3 :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc)
      (add_nonneg (add_nonneg (sq_nonneg _)
        (mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hcb))) (sq_nonneg _)))
      (pow_nonneg (by linarith) 3)
  apply (show Odd 3 by decide).pow_le_pow.mp
  nlinarith only [hid, hnonneg, hr]

theorem schur_identity {a b c r : ℝ} (hr : r ^ 3 = a * b * c) :
    (a + b + c) * (curvature a b c + 3 * r ^ 2) =
      (a - b) ^ 2 * (a + b - c) + c * (a - c) * (b - c) +
        3 * r ^ 2 * (a + b + c - 3 * r) := by
  unfold curvature
  nlinarith only [hr]

private theorem ordered_curvature_lower_bound
    {a b c r : ℝ} (hc : 0 < c) (hcb : c ≤ b) (hba : b ≤ a)
    (hr : r ^ 3 = a * b * c) : -3 * r ^ 2 ≤ curvature a b c := by
  have ham := ordered_arithmetic_geometric hc.le hcb hba hr
  have h1 : 0 ≤ (a - b) ^ 2 * (a + b - c) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have h2 : 0 ≤ c * (a - c) * (b - c) :=
    mul_nonneg (mul_nonneg hc.le (by linarith)) (sub_nonneg.mpr hcb)
  have h3 : 0 ≤ 3 * r ^ 2 * (a + b + c - 3 * r) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sub_nonneg.mpr ham)
  have hprod : 0 ≤ (a + b + c) * (curvature a b c + 3 * r ^ 2) := by
    rw [schur_identity hr]
    exact add_nonneg (add_nonneg h1 h2) h3
  have hsum : 0 < a + b + c := by linarith
  have := (mul_nonneg_iff_of_pos_left hsum).mp hprod
  linarith

/-- The cube-root relation specifies r; neither ordering nor AM-GM is assumed. -/
theorem curvature_lower_bound
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : r ^ 3 = a * b * c) : -3 * r ^ 2 ≤ curvature a b c := by
  rcases le_total b a with hba | hab
  · rcases le_total c b with hcb | hbc
    · exact ordered_curvature_lower_bound hc hcb hba hr
    · rcases le_total c a with hca | hac
      · have h := ordered_curvature_lower_bound hb hbc hca
          (show r ^ 3 = a * c * b by nlinarith only [hr])
        convert h using 1
        unfold curvature
        ring
      · have h := ordered_curvature_lower_bound hb hba hac
          (show r ^ 3 = c * a * b by nlinarith only [hr])
        convert h using 1
        unfold curvature
        ring
  · rcases le_total c a with hca | hac
    · have h := ordered_curvature_lower_bound hc hca hab
        (show r ^ 3 = b * a * c by nlinarith only [hr])
      convert h using 1
      unfold curvature
      ring
    · rcases le_total c b with hcb | hbc
      · have h := ordered_curvature_lower_bound ha hac hcb
          (show r ^ 3 = b * c * a by nlinarith only [hr])
        convert h using 1
        unfold curvature
        ring
      · have h := ordered_curvature_lower_bound ha hab hbc
          (show r ^ 3 = c * b * a by nlinarith only [hr])
        convert h using 1
        unfold curvature
        ring

def correctedDivergence (q h : ℝ) : ℝ := 2 * (q + 4 * h) / (1 + 4 * h)

theorem corrected_divergence_identity
    {q s2 h : ℝ} (hconstraint : s2 + q = 1) (hh : 0 ≤ h) :
    2 * q - 4 * (-2 * s2 * h) / (1 + 4 * h) = correctedDivergence q h := by
  have hden : 1 + 4 * h ≠ 0 := by linarith
  unfold correctedDivergence
  field_simp
  nlinarith [hconstraint]

theorem corrected_divergence_lower_bound
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : r ^ 3 = a * b * c) :
    0 < 2 * r ^ 2 / (1 + 4 * r ^ 2) ∧
      2 * r ^ 2 / (1 + 4 * r ^ 2) ≤ correctedDivergence (curvature a b c) (r ^ 2) := by
  have hrne : r ≠ 0 := by
    intro hz
    have hp := mul_pos (mul_pos ha hb) hc
    rw [hz] at hr
    nlinarith only [hr, hp]
  have hrpos : 0 < r ^ 2 := sq_pos_of_ne_zero hrne
  have hden : 0 < 1 + 4 * r ^ 2 := by positivity
  constructor
  · exact div_pos (mul_pos (by norm_num) hrpos) hden
  · unfold correctedDivergence
    apply (div_le_div_iff_of_pos_right hden).mpr
    have := curvature_lower_bound ha hb hc hr
    linarith

theorem corrected_divergence_pos
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : r ^ 3 = a * b * c) :
    0 < correctedDivergence (curvature a b c) (r ^ 2) := by
  have h := corrected_divergence_lower_bound ha hb hc hr
  exact h.1.trans_le h.2

def wallAmplitude (a b c : ℝ) : ℝ := (a * b * c) ^ (2 / 3 : ℝ)

theorem wallAmplitude_eq_square
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    wallAmplitude a b c = ((a * b * c) ^ (1 / 3 : ℝ)) ^ 2 := by
  rw [← Real.rpow_mul_natCast (mul_pos (mul_pos ha hb) hc).le]
  norm_num [wallAmplitude]

theorem curvature_lower_bound_amplitude
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    -3 * wallAmplitude a b c ≤ curvature a b c := by
  rw [wallAmplitude_eq_square ha hb hc]
  apply curvature_lower_bound ha hb hc
  rw [← Real.rpow_mul_natCast (mul_pos (mul_pos ha hb) hc).le]
  norm_num

theorem corrected_divergence_amplitude_pos
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < correctedDivergence (curvature a b c) (wallAmplitude a b c) := by
  rw [wallAmplitude_eq_square ha hb hc]
  apply corrected_divergence_pos ha hb hc
  rw [← Real.rpow_mul_natCast (mul_pos (mul_pos ha hb) hc).le]
  norm_num

theorem hasDerivAt_wallAmplitude
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t)
    (ha0 : 0 < a t) (hb0 : 0 < b t) (hc0 : 0 < c t) :
    HasDerivAt (fun x => wallAmplitude (a x) (b x) (c x))
      (-2 * shearSq (p t) (s t) * wallAmplitude (a t) (b t) (c t)) t := by
  have hne : a t * b t * c t ≠ 0 := ne_of_gt (mul_pos (mul_pos ha0 hb0) hc0)
  have h := (hasDerivAt_wall_product ha hb hc).rpow_const
    (p := (2 / 3 : ℝ)) (Or.inl hne)
  convert h using 1 <;> first | rfl | (
    unfold wallAmplitude
    rw [Real.rpow_sub_one hne]
    field_simp)

end

end BianchiIX
