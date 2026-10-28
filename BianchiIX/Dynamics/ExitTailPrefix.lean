import BianchiIX.Dynamics.ExitTailMultipliers
import BianchiIX.Algebra.ExitTailPerturbation
import BianchiIX.Analysis.ExitTailIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def exitTailRegion (α b A D : ℝ) (Y : ExitTailState) : Prop :=
  (7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) ∧ |Y 1| ≤ 1 / 100 ∧ |Y 2| ≤ 1 / 100 ∧
    |Y 1| + |Y 2| ≤ A * b ∧ |Y 0 - (2 + 2 * α)| ≤ D * b

def exitTailRateBudget (α b A D T : ℝ) : ℝ :=
  (10 * (α + D * b) + 100 * (A * b) ^ 2) * T + 100 * A * b + 5

theorem exitTailWallRate_abs {α v : ℝ} {Y : ExitTailState} (hα : 0 ≤ α)
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (i : Fin 2) :
    |exitTailWallRate v Y i| ≤ 10 * (α + |Y 0 - (2 + 2 * α)| + v ^ 2) +
      100 * ((|Y 1| + |Y 2|) * v + (|Y 1| + |Y 2|) ^ 2) := by
  have Hp := exitTail_perturbation_bounds hR hu hv hw
  have Hb := exitTail_boundary_rate_small hα hR hv
  fin_cases i
  · change |exitTailStrongRate (Y 0) (Y 1) v (Y 2)| ≤ _
    have H := abs_sub_le (exitTailStrongRate (Y 0) (Y 1) v (Y 2)) (exitTailStrongRate (Y 0) 0 v 0) 0
    simp only [sub_zero] at H
    linarith only [H, Hp.2.1, Hb, abs_nonneg (exitTailWeakRate (Y 0) 0 v 0)]
  · change |exitTailWeakRate (Y 0) (Y 1) v (Y 2)| ≤ _
    have H := abs_sub_le (exitTailWeakRate (Y 0) (Y 1) v (Y 2)) (exitTailWeakRate (Y 0) 0 v 0) 0
    simp only [sub_zero] at H
    linarith only [H, Hp.2.2, Hb, abs_nonneg (exitTailStrongRate (Y 0) 0 v 0)]

theorem exitTail_rate_integral_bound {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) (i : Fin 2) :
    |∫ s in (0 : ℝ)..T, exitTailWallRate (Real.exp (-s)) (Y s) i| ≤ exitTailRateBudget α b A D T := by
  have hv (s : ℝ) (hs : s ∈ Icc 0 T) : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
  have hd (s : ℝ) (hs : s ∈ Icc 0 T) : exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0 := by
    have H := exitTailSpeed_compact (hreg s hs).1.1 (hreg s hs).2.1 (hv s hs) (hreg s hs).2.2.1
    linarith only [H]
  have hc := continuousOn_exitTailWallRate hY hd i
  have H := integral_abs_le_exit_tail_envelope hT (by positivity : 0 ≤ 100 * A * b)
    (by norm_num : (0 : ℝ) ≤ 10) hc (A := 10 * (α + D * b) + 100 * (A * b) ^ 2) ?_
  · apply (intervalIntegral.abs_integral_le_integral_abs hT).trans
    simpa only [exitTailRateBudget, show (10 : ℝ) / 2 = 5 by norm_num] using H
  · intro s hs
    obtain ⟨hR, hu, hw, hsum, hrad⟩ := hreg s hs
    have H' := exitTailWallRate_abs hα hR hu (hv s hs) hw i
    have hsq := (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hA hb)).mpr hsum
    have hm := mul_le_mul_of_nonneg_right hsum (hv s hs).1
    have he : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he] at H'
    nlinarith only [H', hsq, hm, hrad]

theorem exitTail_prefix_multipliers {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s)
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) (i : Fin 2) :
    Y T i.succ = Y 0 i.succ * exitTailMultiplier Y i T ∧
      Real.exp (-exitTailRateBudget α b A D T) ≤ exitTailMultiplier Y i T ∧
      exitTailMultiplier Y i T ≤ Real.exp (exitTailRateBudget α b A D T) := by
  have hd (s : ℝ) (hs : s ∈ Icc 0 T) : exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0 := by
    have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
    have H := exitTailSpeed_compact (hreg s hs).1.1 (hreg s hs).2.1 hv (hreg s hs).2.2.1
    linarith only [H]
  have H := exitTail_rate_integral_bound hT hα hb hA (HasDerivAt.continuousOn hY) hreg i
  exact ⟨(exitTail_wall_multiplier hT hY hd i).1,
    Real.exp_le_exp.mpr (abs_le.mp H).1, Real.exp_le_exp.mpr (abs_le.mp H).2⟩

theorem exitTail_prefix_radial_bound {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hT : 0 ≤ T) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s)
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) :
    |Y T 0 - Y 0 0| ≤ 20 * (A * b + (A * b) ^ 2 * T) := by
  have H := abs_sub_le_integral_bound hT
    (fun s hs => hasDerivAt_pi.mp (hY s hs) 0)
    (B := fun s => 20 * (A * b) ^ 2 + (20 * A * b) * Real.exp (-s) + 0 * Real.exp (-2 * s))
    (by fun_prop) ?_
  · have HI := integral_exit_tail_envelope (T := T) (A := 20 * (A * b) ^ 2)
      (by positivity : 0 ≤ 20 * A * b) (by norm_num : (0 : ℝ) ≤ 0)
    exact H.trans (HI.trans_eq (by ring))
  · intro s hs
    obtain ⟨hR, hu, hw, hsum, _⟩ := hreg s hs
    have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
    have Hp := (exitTail_perturbation_bounds hR hu hv hw).1
    have hsq := (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hA hb)).mpr hsum
    have hU : |Y s 1| ≤ A * b := by linarith only [hsum, abs_nonneg (Y s 2)]
    have hm := mul_le_mul_of_nonneg_right hU hv.1
    change |exitTailRadial (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2)| ≤ _
    nlinarith only [Hp, hsq, hm]

end BianchiIX
