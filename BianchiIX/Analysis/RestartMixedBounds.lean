import BianchiIX.Analysis.RestartCompactBounds
import BianchiIX.Analysis.CompositionDerivativeBounds

noncomputable section

namespace BianchiIX

def restartExpDifferential (n : ℝ) : RestartState →L[ℝ] RestartState :=
  let p : Fin 4 → (RestartState →L[ℝ] ℝ) := fun i => ContinuousLinearMap.proj i
  ContinuousLinearMap.pi ![n • p 0, p 1, p 2, p 3]

theorem hasFDerivAt_restartExpCoordinates (y : RestartState) :
    HasFDerivAt restartExpCoordinates (restartExpDifferential (Real.exp (y 0))) y := by
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).exp
  · exact hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) y
  · exact hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y

theorem restartExpCoordinates_fderiv (y v : RestartState) :
    fderiv ℝ restartExpCoordinates y v = ![Real.exp (y 0) * v 0, v 1, v 2, v 3] := by
  rw [(hasFDerivAt_restartExpCoordinates y).fderiv]
  ext i
  fin_cases i <;> rfl

theorem restartExpCoordinates_fderiv2 (y v w : RestartState) :
    fderiv ℝ (fderiv ℝ restartExpCoordinates) y v w =
      ![Real.exp (y 0) * v 0 * w 0, 0, 0, 0] := by
  have hp (i : Fin 4) : fderiv ℝ (fun z : RestartState => z i) = fun _ => ContinuousLinearMap.proj i :=
    funext (fun z => (hasFDerivAt_apply (𝕜 := ℝ) i z).fderiv)
  have he : fderiv ℝ (fun z : RestartState => Real.exp (z 0)) =
      fun z => Real.exp (z 0) • (ContinuousLinearMap.proj 0 : RestartState →L[ℝ] ℝ) :=
    funext (fun z => (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) z).exp.fderiv)
  have he2 : fderiv ℝ (fderiv ℝ (fun z : RestartState => Real.exp (z 0))) y v w =
      Real.exp (y 0) * v 0 * w 0 := by
    rw [he, (((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y).exp).smul_const
      (ContinuousLinearMap.proj 0 : RestartState →L[ℝ] ℝ)).fderiv]
    rfl
  have H (i : Fin 4) := fderiv2_clm_comp_apply (x := y) (contDiff_restartExpCoordinates 2).contDiffAt
    (ContinuousLinearMap.proj i) v w
  ext i
  fin_cases i
  · have H0 := H 0
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => Real.exp (z 0))) y v w = _ at H0
    exact (he2.symm.trans H0).symm
  · have H1 := H 1
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => z 1)) y v w = _ at H1
    rw [hp, fderiv_const_apply] at H1
    exact H1.symm
  · have H2 := H 2
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => z 2)) y v w = _ at H2
    rw [hp, fderiv_const_apply] at H2
    exact H2.symm
  · have H3 := H 3
    change fderiv ℝ (fderiv ℝ (fun z : RestartState => z 3)) y v w = _ at H3
    rw [hp, fderiv_const_apply] at H3
    exact H3.symm

theorem restartExpCoordinates_derivative_bounds {y : RestartState} (hy : Real.exp (y 0) ≤ 1) :
    ‖fderiv ℝ restartExpCoordinates y‖ ≤ 1 ∧
      ‖fderiv ℝ (fderiv ℝ restartExpCoordinates) y‖ ≤ 1 := by
  have hv (v : RestartState) (i : Fin 4) : |v i| ≤ ‖v‖ := norm_le_pi_norm v i
  have hn : 0 ≤ Real.exp (y 0) := (Real.exp_pos _).le
  have hfirst (v : RestartState) : |Real.exp (y 0) * v 0| ≤ ‖v‖ := by
    rw [abs_mul, abs_of_nonneg hn]
    exact (mul_le_mul_of_nonneg_left (hv v 0) hn).trans (mul_le_of_le_one_left (norm_nonneg v) hy)
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    rw [one_mul, restartExpCoordinates_fderiv]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact hfirst v
    · exact hv v 1
    · exact hv v 2
    · exact hv v 3
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [one_mul, restartExpCoordinates_fderiv2]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg v) (norm_nonneg w))).mpr
    intro i
    fin_cases i
    · change |Real.exp (y 0) * v 0 * w 0| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hfirst v) (hv w 0) (abs_nonneg _) (norm_nonneg v)
    all_goals simpa using mul_nonneg (norm_nonneg v) (norm_nonneg w)

/-- The unbounded logarithmic coordinate has uniform first and second derivative bounds. -/
theorem exists_restartMixed_derivative_bounds :
    ∃ C ≥ (1 : ℝ), ∀ y : RestartState, ‖restartExpCoordinates y‖ ≤ 1 / 16 →
      ‖fderiv ℝ restartMixedField y‖ ≤ C * ‖restartExpCoordinates y‖ ∧
        ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ C := by
  obtain ⟨B, hB, HB⟩ := exists_restartCompact_derivative_bounds
  have hB0 : 0 ≤ B := by linarith only [hB]
  refine ⟨2 * B, by linarith only [hB], ?_⟩
  intro y hy
  have hn : Real.exp (y 0) ≤ 1 := by
    have H : |Real.exp (y 0)| ≤ 1 / 16 := (norm_le_pi_norm (restartExpCoordinates y) 0).trans hy
    rw [abs_of_pos (Real.exp_pos _)] at H
    linarith only [H]
  have hr : 0 < restartRadicand (restartExpCoordinates y) := by
    have H := (restartCompact_box_bounds hy).2.1
    linarith only [H]
  have H := composition_second_derivative_bounds (contDiff_restartExpCoordinates 2).contDiffAt
    (contDiffAt_restartCompactField hr 2) (mul_nonneg hB0 (norm_nonneg _)) hB0 (by norm_num : (0 : ℝ) ≤ 1)
    (restartExpCoordinates_derivative_bounds hn).1 (restartExpCoordinates_derivative_bounds hn).2
    (HB _ hy).1 (HB _ hy).2
  change ‖fderiv ℝ restartMixedField y‖ ≤ B * ‖restartExpCoordinates y‖ * 1 ∧
    ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ B * ‖restartExpCoordinates y‖ * 1 + B * 1 ^ 2 at H
  constructor
  · nlinarith only [H.1, mul_nonneg hB0 (norm_nonneg (restartExpCoordinates y))]
  · nlinarith only [H.2, mul_le_mul_of_nonneg_left hy hB0, hB0]

def restartMixedBox : Set RestartState :=
  Set.pi Set.univ (fun i => if i = 0 then Set.Iic (Real.log (1 / 16)) else Set.Icc (-(1 / 16)) (1 / 16))

theorem convex_restartMixedBox : Convex ℝ restartMixedBox := by
  apply convex_pi
  intro i _
  split_ifs
  · exact convex_Iic _
  · exact convex_Icc _ _

theorem mem_restartMixedBox_iff (y : RestartState) :
    y ∈ restartMixedBox ↔ ‖restartExpCoordinates y‖ ≤ 1 / 16 := by
  have hlog : y 0 ≤ Real.log (1 / 16) ↔ Real.exp (y 0) ≤ 1 / 16 :=
    Real.le_log_iff_exp_le (by norm_num)
  constructor
  · intro hy
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 16)).mpr
    intro i
    have H := hy i (Set.mem_univ i)
    fin_cases i
    · change y 0 ≤ Real.log (1 / 16) at H
      change |Real.exp (y 0)| ≤ 1 / 16
      rw [abs_of_pos (Real.exp_pos _)]
      exact hlog.mp H
    · exact abs_le.mpr H
    · exact abs_le.mpr H
    · exact abs_le.mpr H
  · intro hy i _
    have H := (norm_le_pi_norm (restartExpCoordinates y) i).trans hy
    fin_cases i
    · change y 0 ≤ Real.log (1 / 16)
      apply hlog.mpr
      change |Real.exp (y 0)| ≤ 1 / 16 at H
      simpa only [abs_of_pos (Real.exp_pos _)] using H
    · exact abs_le.mp H
    · exact abs_le.mp H
    · exact abs_le.mp H

theorem restartExpCoordinates_norm_le {y : RestartState} {r : ℝ} (hr : 0 ≤ r)
    (hs : |y 1| ≤ r) (ha : |y 2| ≤ r) (hb : |y 3| ≤ r) :
    ‖restartExpCoordinates y‖ ≤ Real.exp (y 0) + r := by
  have hn := (Real.exp_pos (y 0)).le
  apply (pi_norm_le_iff_of_nonneg (add_nonneg hn hr)).mpr
  intro i
  fin_cases i
  · change |Real.exp (y 0)| ≤ _
    rw [abs_of_nonneg hn]
    linarith only [hr]
  · change |y 1| ≤ _
    linarith only [hs, hn]
  · change |y 2| ≤ _
    linarith only [ha, hn]
  · change |y 3| ≤ _
    linarith only [hb, hn]

/-- One constant controls the derivatives and their differences throughout the full logarithmic strip. -/
theorem exists_restartMixed_uniform_bounds :
    ∃ C ≥ (1 : ℝ),
      (∀ y : RestartState, ‖restartExpCoordinates y‖ ≤ 1 / 16 →
        ‖fderiv ℝ restartMixedField y‖ ≤ C * ‖restartExpCoordinates y‖ ∧
          ‖fderiv ℝ (fderiv ℝ restartMixedField) y‖ ≤ C) ∧
      (∀ y z : RestartState, ‖restartExpCoordinates y‖ ≤ 1 / 16 →
        ‖restartExpCoordinates z‖ ≤ 1 / 16 →
        ‖fderiv ℝ restartMixedField y - fderiv ℝ restartMixedField z‖ ≤ C * ‖y - z‖) := by
  obtain ⟨C, hC, HC⟩ := exists_restartMixed_derivative_bounds
  refine ⟨C, hC, HC, ?_⟩
  intro y z hy hz
  have hdiff (x : RestartState) (hx : x ∈ restartMixedBox) :
      DifferentiableAt ℝ (fderiv ℝ restartMixedField) x := by
    have H := (restartCompact_box_bounds ((mem_restartMixedBox_iff x).mp hx)).2.1
    exact ((contDiffAt_restartMixedField (by linarith only [H]) 2).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hbound (x : RestartState) (hx : x ∈ restartMixedBox) :
      ‖fderiv ℝ (fderiv ℝ restartMixedField) x‖ ≤ C := (HC x ((mem_restartMixedBox_iff x).mp hx)).2
  exact Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound convex_restartMixedBox
    ((mem_restartMixedBox_iff z).mpr hz) ((mem_restartMixedBox_iff y).mpr hy)

end BianchiIX
