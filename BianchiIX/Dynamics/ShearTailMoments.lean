import BianchiIX.Dynamics.ShearTailControl
import BianchiIX.Analysis.DissipativeMoments
import BianchiIX.Analysis.CoreIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def shearTailEnergy (z : NormalizedState) : ℝ :=
  z 2 ^ 2 + z 3 ^ 2 + z 4 ^ 2 + z 2 * (z 3 + z 4)

/-- The fast terms share one dissipative rate; only the growing square uses the tail duration. -/
theorem shearTail_prefix_moments {a T : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hT : 0 ≤ T)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, shearTailRegion a (α t)) :
    (∫ t in 0..T, shearTailEnergy (α t)) ≤
      (2 / 3 : ℝ) * (α 0 2 ^ 2 + α 0 2 * (α 0 3 + α 0 4)) + α 0 4 ^ 2 / a +
        α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * T) ∧
    (∫ t in 0..T, t * shearTailEnergy (α t)) ≤
      (4 / 9 : ℝ) * (α 0 2 ^ 2 + α 0 2 * (α 0 3 + α 0 4)) + α 0 4 ^ 2 / a ^ 2 +
        T * (α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * T)) := by
  let f : ℝ → ℝ := fun t => α t 2 ^ 2 + α t 2 * (α t 3 + α t 4)
  let r (i : Fin 3) (t : ℝ) : ℝ :=
    ![rateOne (α t 0) (α t 1), rateTwo (α t 0) (α t 1), rateThree (α t 0) (α t 1)] i
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      r 0 t ≤ -2 ∧ r 1 t ≤ 6 * a ∧ r 2 t ≤ -a / 2 := by
    obtain ⟨hp, hsl, hsu, hN, hX, hY⟩ := hregion t ht
    have H := shearTail_wall_rates ha (by linarith only [hp]) ⟨hsl, hsu⟩
      ⟨(hn t ht).1, hN⟩ ⟨(hn t ht).2.1, hX⟩ ⟨(hn t ht).2.2, hY⟩ (hc t ht)
    exact ⟨H.1, (le_abs_self _).trans H.2.1, H.2.2⟩
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := hasDerivAt_normalized_components (hα t ht)
  have HF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt f (2 * r 0 t * α t 2 ^ 2 + (r 0 t + r 1 t) * (α t 2 * α t 3) +
        (r 0 t + r 2 t) * (α t 2 * α t 4)) t := by
    convert! ((HD t ht).2.2.1.pow 2).add
      ((HD t ht).2.2.1.mul ((HD t ht).2.2.2.1.add (HD t ht).2.2.2.2)) using 1
    dsimp [r]
    ring
  have HFdec (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      2 * r 0 t * α t 2 ^ 2 + (r 0 t + r 1 t) * (α t 2 * α t 3) +
        (r 0 t + r 2 t) * (α t 2 * α t 4) ≤ -(3 / 2 : ℝ) * f t := by
    have H1 := mul_le_mul_of_nonneg_right (HR t ht).1 (sq_nonneg (α t 2))
    have H2 := mul_le_mul_of_nonneg_right
      (show r 0 t + r 1 t ≤ -(3 / 2 : ℝ) by linarith only [(HR t ht).1, (HR t ht).2.1, ha.2])
      (mul_nonneg (hn t ht).1 (hn t ht).2.1)
    have H3 := mul_le_mul_of_nonneg_right
      (show r 0 t + r 2 t ≤ -(3 / 2 : ℝ) by linarith only [(HR t ht).1, (HR t ht).2.2, ha.1])
      (mul_nonneg (hn t ht).1 (hn t ht).2.2)
    dsimp only [f]
    nlinarith only [H1, H2, H3, sq_nonneg (α t 2)]
  have HFM := integral_moments_le_of_linear_dissipation hT (by norm_num : (0 : ℝ) < 3 / 2)
    HF HFdec (by dsimp only [f]; positivity [(hn T ⟨hT, le_rfl⟩).1,
      (hn T ⟨hT, le_rfl⟩).2.1, (hn T ⟨hT, le_rfl⟩).2.2])
  have HYD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun t => α t 4 ^ 2) (2 * r 2 t * α t 4 ^ 2) t := by
    convert! (HD t ht).2.2.2.2.pow 2 using 1
    dsimp [r]
    ring
  have HYM := integral_moments_le_of_linear_dissipation hT ha.1 HYD (fun t ht => by
    have H := mul_le_mul_of_nonneg_right (HR t ht).2.2 (sq_nonneg (α t 4))
    nlinarith only [H]) (sq_nonneg (α T 4))
  have HXD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun t => α t 3 ^ 2) (2 * r 1 t * α t 3 ^ 2) t := by
    convert! (HD t ht).2.2.2.1.pow 2 using 1
    dsimp [r]
    ring
  have HX (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      α t 3 ^ 2 ≤ α 0 3 ^ 2 * Real.exp (12 * a * t) := by
    have H := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T) HXD (c := 12 * a)
      (fun u hu => by
        have H := mul_le_mul_of_nonneg_right (HR u hu).2.1 (sq_nonneg (α u 3))
        nlinarith only [H]) ⟨le_rfl, hT⟩ ht ht.1
    simpa only [sub_zero] using H
  have HGD (t : ℝ) : HasDerivAt (fun t => α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * t))
      (α 0 3 ^ 2 * Real.exp (12 * a * t)) t := by
    convert! (((hasDerivAt_id' t).const_mul (12 * a)).exp.const_mul (α 0 3 ^ 2 / (12 * a))) using 1
    field_simp [ha.1.ne']
  have hxcont := HasDerivAt.continuousOn HXD
  have hycont := HasDerivAt.continuousOn HYD
  have hfcont := HasDerivAt.continuousOn HF
  have hgcont : Continuous (fun t => α 0 3 ^ 2 * Real.exp (12 * a * t)) := by fun_prop
  have HXM : (∫ t in 0..T, α t 3 ^ 2) ≤ α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * T) := by
    have H := intervalIntegral.integral_mono_on (μ := volume) hT (hxcont.intervalIntegrable_of_Icc hT)
      (hgcont.intervalIntegrable _ _) HX
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => HGD t) (hgcont.intervalIntegrable _ _)] at H
    simp only [mul_zero, Real.exp_zero, mul_one] at H
    exact H.trans (sub_le_self _ (by positivity [ha.1]))
  have HXTM : (∫ t in 0..T, t * α t 3 ^ 2) ≤
      T * (α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * T)) := by
    have H := intervalIntegral.integral_mono_on (μ := volume) hT
      ((continuousOn_id.mul hxcont).intervalIntegrable_of_Icc hT)
      ((continuousOn_const.mul hxcont).intervalIntegrable_of_Icc hT)
      (fun t ht => mul_le_mul_of_nonneg_right ht.2 (sq_nonneg (α t 3)))
    simp only [Pi.mul_apply, id_eq] at H
    rw [intervalIntegral.integral_const_mul] at H
    exact H.trans (mul_le_mul_of_nonneg_left HXM hT)
  have he (t : ℝ) : shearTailEnergy (α t) = f t + α t 4 ^ 2 + α t 3 ^ 2 := by
    dsimp only [shearTailEnergy, f]
    ring
  simp only [sub_zero] at HFM HYM
  constructor
  · simp_rw [he]
    rw [intervalIntegral.integral_add (f := fun t => f t + α t 4 ^ 2) (g := fun t => α t 3 ^ 2)
      ((hfcont.add hycont).intervalIntegrable_of_Icc hT)
      (hxcont.intervalIntegrable_of_Icc hT),
      intervalIntegral.integral_add (hfcont.intervalIntegrable_of_Icc hT) (hycont.intervalIntegrable_of_Icc hT)]
    dsimp only [f] at HFM
    linarith only [HFM.1, HYM.1, HXM]
  · simp_rw [he, mul_add]
    rw [intervalIntegral.integral_add (f := fun t => t * f t + t * α t 4 ^ 2) (g := fun t => t * α t 3 ^ 2)
      (((continuousOn_id.mul hfcont).add (continuousOn_id.mul hycont)).intervalIntegrable_of_Icc hT)
      ((continuousOn_id.mul hxcont).intervalIntegrable_of_Icc hT),
      intervalIntegral.integral_add (f := fun t => t * f t) (g := fun t => t * α t 4 ^ 2)
        ((continuousOn_id.mul hfcont).intervalIntegrable_of_Icc hT)
        ((continuousOn_id.mul hycont).intervalIntegrable_of_Icc hT)]
    have Hsum := add_le_add (add_le_add HFM.2 HYM.2) HXTM
    dsimp only [f] at Hsum
    convert! Hsum using 1
    ring

theorem normalized_shearTail_moments {a A X Y T : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hT : 0 ≤ T)
    (hA : 0 ≤ A ∧ A < a ^ 2)
    (hX : 0 ≤ X ∧ X * Real.exp (6 * a * T) < a ^ 2)
    (hY : 0 ≤ Y ∧ Y < a / 16)
    (hc : stateConstraint z = 1) (hp : z 0 < 0)
    (hs : 3 * a / 4 ≤ z 1 ∧ z 1 ≤ 9 * a / 4)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hinit : z 2 ≤ A ∧ z 3 ≤ X ∧ z 4 ≤ Y) :
    (∫ t in 0..T, shearTailEnergy (normalizedMaxCurve z 0 t)) ≤
      (2 / 3 : ℝ) * (A ^ 2 + A * (X + Y)) + Y ^ 2 / a + X ^ 2 / (12 * a) * Real.exp (12 * a * T) ∧
    (∫ t in 0..T, t * shearTailEnergy (normalizedMaxCurve z 0 t)) ≤
      (4 / 9 : ℝ) * (A ^ 2 + A * (X + Y)) + Y ^ 2 / a ^ 2 +
        T * (X ^ 2 / (12 * a) * Real.exp (12 * a * T)) := by
  have Hcontrol := normalized_shearTail_control ha hT hA hX hY hc hp hs hn hinit
  have H := shearTail_prefix_moments ha hT
    (fun t ht => (normalizedMaxCurve_forward_of_constraint hc ht.1).1)
    (fun t ht => (normalizedMaxCurve_forward_of_constraint hc ht.1).2.1)
    (fun t ht => ⟨(normalizedMaxCurve_wall_sign hc ht.1 (0 : Fin 3)).2.mpr hn.1,
      (normalizedMaxCurve_wall_sign hc ht.1 (1 : Fin 3)).2.mpr hn.2.1,
      (normalizedMaxCurve_wall_sign hc ht.1 (2 : Fin 3)).2.mpr hn.2.2⟩)
    (fun t ht => (Hcontrol t ht).2.1)
  rw [normalizedMaxCurve_initial] at H
  have HN := pow_le_pow_left₀ hn.1 hinit.1 2
  have HX := pow_le_pow_left₀ hn.2.1 hinit.2.1 2
  have HY := pow_le_pow_left₀ hn.2.2 hinit.2.2 2
  have HF := add_le_add HN (mul_le_mul hinit.1 (add_le_add hinit.2.1 hinit.2.2)
    (add_nonneg hn.2.1 hn.2.2) hA.1)
  have ha0 : 0 ≤ a := ha.1.le
  constructor
  · apply H.1.trans
    gcongr
  · apply H.2.trans
    gcongr

end BianchiIX
