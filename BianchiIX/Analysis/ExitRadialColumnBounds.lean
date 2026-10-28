import BianchiIX.Analysis.ExitTailRateBounds
import BianchiIX.Analysis.ForcedDecayIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem exitTailField_radial_direction_bound {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (ξ : ExitTailState) :
    |fderiv ℝ (exitTailField v) Y ξ 0| ≤
      256 * (|Y 1| * v + (|Y 1| + |Y 2|) ^ 2) * |ξ 0| +
      32 * (v + |Y 1| + |Y 2|) * |ξ 1| + 16 * (|Y 1| + |Y 2|) * |ξ 2| := by
  have hvR : v ^ 2 < (Y 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  have hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0 := by
    have H := exitTailSpeed_compact hR.1 hu hv hw
    linarith only [H]
  rw [exitTailField_fderiv (by linarith only [hR.1]) hvR hd]
  change |∑ i : Fin 3, exitTailRadialGradient (Y 0) (Y 1) v (Y 2) i * ξ i| ≤ _
  rw [Fin.sum_univ_three]
  have HG := exitTail_radial_gradient_bounds hR hu hv hw
  have H := abs_add_three (exitTailRadialGradient (Y 0) (Y 1) v (Y 2) 0 * ξ 0)
    (exitTailRadialGradient (Y 0) (Y 1) v (Y 2) 1 * ξ 1)
    (exitTailRadialGradient (Y 0) (Y 1) v (Y 2) 2 * ξ 2)
  simp only [abs_mul] at H
  exact H.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right HG.1 (abs_nonneg _))
    (mul_le_mul_of_nonneg_right HG.2.1 (abs_nonneg _)))
    (mul_le_mul_of_nonneg_right HG.2.2 (abs_nonneg _)))

/-- A direction with no initial strong-wall component has a directly integrable radial response. -/
theorem exitTail_radial_column_envelope {v K a b s n d : ℝ} {Y ξ : ExitTailState}
    (hK : 1 ≤ K) (ha : 0 ≤ a) (hab : a ≤ b) (hs : 0 ≤ s) (hn : 0 ≤ n) (hd : 0 ≤ d)
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100)
    (hamp : |Y 1| ≤ K * a) (hsum : |Y 1| + |Y 2| ≤ K * b)
    (hξ0 : |ξ 0| ≤ K * n) (hξ1 : |ξ 1| ≤ K ^ 2 * a * s * n)
    (hξ2 : |ξ 2| ≤ K * d + K ^ 2 * b * s * n) :
    |fderiv ℝ (exitTailField v) Y ξ 0| ≤
      512 * K ^ 3 * ((a * (1 + s) * v + b ^ 2 * (1 + s)) * n + b * d) := by
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hb : 0 ≤ b := ha.trans hab
  have hv0 : 0 ≤ v := hv.1
  have hKK : K ≤ K ^ 2 := by nlinarith only [hK]
  have hKKK : K ^ 2 ≤ K ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
  have h0 : 256 * (|Y 1| * v + (|Y 1| + |Y 2|) ^ 2) * |ξ 0| ≤
      256 * K ^ 3 * (a * v + b ^ 2) * n := by
    calc
      _ ≤ 256 * (K * a * v + (K * b) ^ 2) * (K * n) := by gcongr
      _ = 256 * (K ^ 2 * a * v + K ^ 3 * b ^ 2) * n := by ring
      _ ≤ 256 * (K ^ 3 * a * v + K ^ 3 * b ^ 2) * n := by gcongr
      _ = _ := by ring
  have h1 : 32 * (v + |Y 1| + |Y 2|) * |ξ 1| ≤
      32 * K ^ 3 * (a * s * v + b ^ 2 * s) * n := by
    calc
      _ = 32 * (v + (|Y 1| + |Y 2|)) * |ξ 1| := by ring
      _ ≤ 32 * (v + K * b) * (K ^ 2 * a * s * n) := by gcongr
      _ = 32 * (K ^ 2 * a * s * v + K ^ 3 * (b * a) * s) * n := by ring
      _ ≤ 32 * (K ^ 3 * a * s * v + K ^ 3 * (b * b) * s) * n := by gcongr
      _ = _ := by ring
  have h2 : 16 * (|Y 1| + |Y 2|) * |ξ 2| ≤
      16 * K ^ 3 * (b * d + b ^ 2 * s * n) := by
    calc
      _ ≤ 16 * (K * b) * (K * d + K ^ 2 * b * s * n) := by gcongr
      _ = 16 * (K ^ 2 * b * d + K ^ 3 * b ^ 2 * s * n) := by ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hKKK (mul_nonneg hb hd)]
  have H := (exitTailField_radial_direction_bound hR hu hv hw ξ).trans (add_le_add (add_le_add h0 h1) h2)
  have hp : 0 ≤ K ^ 3 * a * v * n := by positivity
  have hps : 0 ≤ K ^ 3 * a * s * v * n := by positivity
  have hq : 0 ≤ K ^ 3 * b ^ 2 * n := by positivity
  have hqs : 0 ≤ K ^ 3 * b ^ 2 * s * n := by positivity
  have hbd : 0 ≤ K ^ 3 * b * d := by positivity
  nlinarith only [H, hp, hps, hq, hqs, hbd]

theorem integral_exit_radial_column_envelope {T a b n d : ℝ}
    (hT : 0 ≤ T) (ha : 0 ≤ a) (hn : 0 ≤ n) :
    (∫ s in (0 : ℝ)..T, (a * (1 + s) * Real.exp (-s) + b ^ 2 * (1 + s)) * n + b * d) ≤
      (2 * a + b ^ 2 * T * (1 + T)) * n + b * d * T := by
  have HC : Continuous (fun s : ℝ => a * (1 + s) * Real.exp (-s)) := by fun_prop
  have HP : Continuous (fun s : ℝ => b ^ 2 * (1 + s)) := by fun_prop
  have HE : (∫ s in (0 : ℝ)..T, a * (1 + s) * Real.exp (-s)) ≤ 2 * a := by
    have H := integral_le_of_affine_exp_decay hT (by norm_num : (0 : ℝ) < 1) ha ha
      HC.continuousOn (fun s _ => le_of_eq (by simp only [sub_zero, neg_mul, one_mul]; ring))
    simpa only [div_one, one_pow, ← two_mul] using H
  have HB : (∫ s in (0 : ℝ)..T, b ^ 2 * (1 + s)) ≤ b ^ 2 * T * (1 + T) := by
    have H := intervalIntegral.integral_mono_on (μ := volume) hT (HP.intervalIntegrable _ _)
      (intervalIntegrable_const (c := b ^ 2 * (1 + T))) (fun s hs => by gcongr; exact hs.2)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at H
    exact H.trans_eq (by ring)
  have HI : IntervalIntegrable (fun s : ℝ => (a * (1 + s) * Real.exp (-s) + b ^ 2 * (1 + s)) * n) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ => (a * (1 + s) * Real.exp (-s) + b ^ 2 * (1 + s)) * n)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add HI (intervalIntegrable_const),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_add (HC.intervalIntegrable _ _) (HP.intervalIntegrable _ _),
    intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  nlinarith only [mul_le_mul_of_nonneg_right (add_le_add HE HB) hn]

end BianchiIX
