import BianchiIX.Dynamics.CompactConnectionWeakRadial

noncomputable section

namespace BianchiIX

open Set

/-- Equation (B.49), on a common signed neighborhood of the actual finite tail. -/
theorem exists_compact_connection_finite_radial_bound {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y ∧
        |fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single 0 1) - 1| ≤
          C * (|Y 1| + (Y 2) ^ 2) := by
  obtain ⟨εF, hεF, A, hA, HA⟩ := exists_compact_connection_finite_phase_bounds hη
  obtain ⟨εQ, hεQ, B, hB, HB⟩ := exists_compact_connection_weak_radial_bound hη
  let ε := min εF εQ
  have hε : 0 < ε := lt_min hεF hεQ
  let F := compactConnectionFinitePhase η
  let S : Set CoreAngleState := Icc (![31 / 8, -ε, -ε] : CoreAngleState) ![6, ε, ε]
  have hcoords {Y : CoreAngleState} (hY : Y ∈ S) :
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) ∧ |Y 1| ≤ ε ∧ |Y 2| ≤ ε :=
    ⟨⟨hY.1 0, hY.2 0⟩, abs_le.mpr ⟨hY.1 1, hY.2 1⟩, abs_le.mpr ⟨hY.1 2, hY.2 2⟩⟩
  have hmem {Y : CoreAngleState} (hk : 31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6)
      (hu : |Y 1| ≤ ε) (hw : |Y 2| ≤ ε) : Y ∈ S := by
    constructor
    · intro i
      fin_cases i
      · exact hk.1
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · intro i
      fin_cases i
      · exact hk.2
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have hreg (Y : CoreAngleState) (hY : Y ∈ S) := HA Y (hcoords hY).1
    ((hcoords hY).2.1.trans (min_le_left _ _)) ((hcoords hY).2.2.trans (min_le_left _ _))
  have hdiff (Y : CoreAngleState) (hY : Y ∈ S) : DifferentiableAt ℝ (fderiv ℝ F) Y :=
    (((hreg Y hY).2.1).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hbound (Y : CoreAngleState) (hY : Y ∈ S) : ‖fderiv ℝ (fderiv ℝ F) Y‖ ≤ A := by
    have H := (hreg Y hY).2.2
    change |F Y| + ‖fderiv ℝ F Y‖ + ‖fderiv ℝ (fderiv ℝ F) Y‖ ≤ A at H
    linarith only [H, abs_nonneg (F Y), norm_nonneg (fderiv ℝ F Y)]
  refine ⟨ε, hε, A + B, add_pos hA hB, ?_⟩
  intro Y hk hu hw
  let Z : CoreAngleState := ![Y 0, 0, Y 2]
  have hY : Y ∈ S := hmem hk hu hw
  have hZ : Z ∈ S := hmem hk (by simpa only [Z, Matrix.cons_val_one, Matrix.cons_val_zero, abs_zero] using hε.le) hw
  have Hdiff := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_Icc _ _) hZ hY
  have hdist : ‖Y - Z‖ ≤ |Y 1| := by
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg (Y 1))).mpr
    intro i
    fin_cases i
    · change |Y 0 - Y 0| ≤ |Y 1|
      simpa only [sub_self, abs_zero] using abs_nonneg (Y 1)
    · change |Y 1 - 0| ≤ |Y 1|
      simp only [sub_zero, le_refl]
    · change |Y 2 - Y 2| ≤ |Y 1|
      simpa only [sub_self, abs_zero] using abs_nonneg (Y 1)
  have hnorm : ‖fderiv ℝ F Y - fderiv ℝ F Z‖ ≤ A * |Y 1| :=
    Hdiff.trans (mul_le_mul_of_nonneg_left hdist hA.le)
  have hcol : |fderiv ℝ F Y (Pi.single 0 1) - fderiv ℝ F Z (Pi.single 0 1)| ≤ A * |Y 1| := by
    have H := (fderiv ℝ F Y - fderiv ℝ F Z).le_opNorm (Pi.single 0 1)
    have H' : |fderiv ℝ F Y (Pi.single 0 1) - fderiv ℝ F Z (Pi.single 0 1)| ≤
        ‖fderiv ℝ F Y - fderiv ℝ F Z‖ := by
      simpa only [sub_apply, Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using H
    exact H'.trans hnorm
  have hweak : |fderiv ℝ F Z (Pi.single 0 1) - 1| ≤ B * (Y 2) ^ 2 :=
    HB (Y 0) hk (Y 2) (hw.trans (min_le_right _ _))
  refine ⟨(hreg Y hY).1, (hreg Y hY).2.1, ?_⟩
  calc
    _ ≤ |fderiv ℝ F Y (Pi.single 0 1) - fderiv ℝ F Z (Pi.single 0 1)| +
        |fderiv ℝ F Z (Pi.single 0 1) - 1| := abs_sub_le _ _ _
    _ ≤ A * |Y 1| + B * (Y 2) ^ 2 := add_le_add hcol hweak
    _ ≤ (A + B) * (|Y 1| + (Y 2) ^ 2) := by
      nlinarith only [mul_nonneg hB.le (abs_nonneg (Y 1)), mul_nonneg hA.le (sq_nonneg (Y 2))]

end BianchiIX
