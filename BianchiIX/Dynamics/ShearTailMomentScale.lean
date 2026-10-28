import BianchiIX.Dynamics.ShearTailScale
import BianchiIX.Dynamics.ShearTailMoments

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The regional wall scales give linear moment budgets without expanding every small power. -/
theorem shearTail_moment_bounds_linear {a D n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1) (hD : 0 ≤ D)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16)
    (hX : x * Real.exp (6 * a * shearTailTime a D) ≤ a ^ 2) :
    (2 / 3 : ℝ) * (n ^ 2 + n * (x + y)) + y ^ 2 / a +
      x ^ 2 / (12 * a) * Real.exp (12 * a * shearTailTime a D) ≤ 4 * a ∧
    (4 / 9 : ℝ) * (n ^ 2 + n * (x + y)) + y ^ 2 / a ^ 2 +
      shearTailTime a D * (x ^ 2 / (12 * a) * Real.exp (12 * a * shearTailTime a D)) ≤
      1 / 256 + (2 + D) * a := by
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha.2]
  have ha3 : a ^ 3 ≤ a := by
    have H := mul_le_mul_of_nonneg_left ha2 ha.1.le
    nlinarith only [H, ha2]
  have ha4 : a ^ 4 ≤ a ^ 3 := by
    have H := mul_le_mul_of_nonneg_right ha.2 (pow_nonneg ha.1.le 3)
    nlinarith only [H]
  have HF : n ^ 2 + n * (x + y) ≤ 3 * a ^ 3 := by
    have Hn := pow_le_pow_left₀ hn.1 hn.2 2
    have Hy : y ≤ a := hy.2.trans (by linarith only [ha.1])
    have Hxy := mul_le_mul hn.2 (add_le_add hx.2 Hy) (add_nonneg hx.1 hy.1) (sq_nonneg a)
    nlinarith only [Hn, Hxy, ha4]
  have HY := pow_le_pow_left₀ hy.1 hy.2 2
  have HY0 : y ^ 2 / a ≤ a / 256 := (div_le_iff₀ ha.1).mpr (by nlinarith only [HY])
  have HY1 : y ^ 2 / a ^ 2 ≤ 1 / 256 := (div_le_iff₀ (sq_pos_of_pos ha.1)).mpr (by nlinarith only [HY])
  have he : Real.exp (12 * a * shearTailTime a D) = Real.exp (6 * a * shearTailTime a D) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have HXsq := pow_le_pow_left₀ (mul_nonneg hx.1 (Real.exp_pos _).le) hX 2
  rw [mul_pow, ← he] at HXsq
  have HX0 : x ^ 2 / (12 * a) * Real.exp (12 * a * shearTailTime a D) ≤ a ^ 3 / 12 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity [ha.1] : 0 < 12 * a)).mpr
    nlinarith only [HXsq]
  have hlog : 0 ≤ Real.log (1 / a) := Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa using ha.2))
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le) hlog
  have halog : a * Real.log (1 / a) ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (one_div_pos.mpr ha.1)) ha.1.le
    have heq : a * (1 / a - 1) = 1 - a := by field_simp [ha.1.ne']
    rw [heq] at H
    linarith only [H, ha.1]
  have HX1 : shearTailTime a D * (x ^ 2 / (12 * a) * Real.exp (12 * a * shearTailTime a D)) ≤ D * a := by
    apply (mul_le_mul_of_nonneg_left HX0 hT).trans
    have heq : shearTailTime a D * (a ^ 3 / 12) = (D * a / 12) * (a * Real.log (1 / a)) := by
      dsimp only [shearTailTime]
      field_simp [ha.1.ne']
    rw [heq]
    have H := mul_le_mul_of_nonneg_left halog (by positivity [ha.1] : 0 ≤ D * a / 12)
    nlinarith only [H, mul_nonneg hD ha.1.le]
  constructor
  · nlinarith only [HF, HY0, HX0, ha3, ha.1]
  · nlinarith only [HF, HY1, HX1, ha3, ha.1]

/-- The actual controlled tail has a vanishing zeroth moment and a uniformly small first moment. -/
theorem shearTail_prefix_moments_linear {a D : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hD : 0 ≤ D)
    (hα : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hr : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), shearTailRegion a (α t))
    (hX : α 0 3 * Real.exp (6 * a * shearTailTime a D) ≤ a ^ 2) :
    (∫ t in 0..shearTailTime a D, shearTailEnergy (α t)) ≤ 4 * a ∧
    (∫ t in 0..shearTailTime a D, t * shearTailEnergy (α t)) ≤ 1 / 256 + (2 + D) * a := by
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa using ha1)))
  obtain ⟨_, _, _, hN, hX0, hY⟩ := hr 0 ⟨le_rfl, hT⟩
  have Hn := hn 0 ⟨le_rfl, hT⟩
  have H := shearTail_prefix_moments ha hT hα hc hn hr
  have HB := shearTail_moment_bounds_linear ⟨ha.1, ha1⟩ hD ⟨Hn.1, hN⟩ ⟨Hn.2.1, hX0⟩ ⟨Hn.2.2, hY⟩ hX
  exact ⟨H.1.trans HB.1, H.2.trans HB.2⟩

end BianchiIX
