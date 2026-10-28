import BianchiIX.Dynamics.ExitSinglePhaseDifferential

noncomputable section

namespace BianchiIX

theorem exitSingle_terminal_error_bounds {α b R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hb : b ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ α / 10000)
    (hw : |u| + |w| ≤ b) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    2 < Real.sqrt (R ^ 2 + exitSingleError R u v w) ∧
      |exitSingleError R u v w| ≤ 46 * b * (v + b) / α ∧
      |exitSingleErrorRadial R u v w| ≤ 900 * b * (v + b) / α ^ 2 ∧
      |exitSingleErrorWallFactor R u v w| ≤ 24 / α := by
  have hα0 := hα.1
  obtain ⟨HR, HRhi, HG, HGhi, Hsq, HH, HT, HN, HHpos, HNpos⟩ :=
    exitSingle_terminal_geometry hα hb hR hw hv
  have HH₀ : 0 < exitSingleBase R v := lt_of_lt_of_le (sq_pos_of_pos hα0) HH
  have HG0 : 0 < exitTailGap R v := lt_trans (by norm_num) HG
  have HR0 : 0 ≤ R := by linarith only [HR]
  have Hoffset := exitTailGap_terminal_offset hα (le_refl (α / 10000)) hR hv
  have HGdiff : exitTailGap R v - 2 ≤ 3 * α := by linarith only [Hoffset.2, hα.1]
  have HL : |exitSingleBaseRadial R v| ≤ 20 * α := by
    rw [exitSingleBaseRadial, abs_of_nonneg (by positivity)]
    calc
      _ ≤ 2 * (3 * α) * 5 / 2 := by gcongr
      _ ≤ _ := by linarith only [hα.1]
  have HE := exitSingleError_scalar_bounds hα ⟨HR0, HRhi⟩ HH HT HN HL
    (exitSingleDefect_bound hv.1 hw)
  have HS : 4 < R ^ 2 + exitSingleError R u v w := by
    rw [exitSingleSquare_eq HH₀.ne']
    linarith only [div_pos (mul_pos HHpos HNpos) HH₀]
  refine ⟨(Real.lt_sqrt (by norm_num)).mpr (by norm_num; exact HS), ?_, ?_, HE.2.2.2⟩
  · have H := HE.1
    change |exitSingleError R u v w| ≤ 23 * (2 * b * (v + b)) / α at H
    convert H using 1; ring
  · have H := HE.2.2.1
    change |exitSingleErrorRadial R u v w| ≤ 450 * (2 * b * (v + b)) / α ^ 2 at H
    convert H using 1; ring

/-- Ordinary fixed-height derivatives, including signed and zero old walls, with the radial cancellation. -/
theorem exitSinglePhase_derivative_bounds {α b v : ℝ} {Y : ExitTailState}
    (hα : 0 < α ∧ α ≤ 1) (hb : b ≤ α / 10000)
    (hR : |Y 0 - (2 + 2 * α)| ≤ α / 10000) (hw : |Y 1| + |Y 2| ≤ b)
    (hv : 0 ≤ v ∧ v ≤ α / 100) :
    let f := fun Z : ExitTailState => exitSinglePhase (Z 0) (Z 1) v (Z 2)
    ContDiffAt ℝ 2 f Y ∧
      |fderiv ℝ f Y (Pi.single 0 1) - 1 / 2| ≤ 1024 * b * (v + b) / α ^ 2 ∧
      |fderiv ℝ f Y (Pi.single 1 1)| + |fderiv ℝ f Y (Pi.single 2 1)| ≤ 1024 * (v + b) / α := by
  intro f
  have hα0 := hα.1
  have hv0 := hv.1
  have hb0 : 0 ≤ b := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  obtain ⟨HR, HRhi, HG, HGhi, Hsq, HH, HT, HN, HHpos, HNpos⟩ :=
    exitSingle_terminal_geometry hα hb hR hw hv
  have HH₀ : 0 < exitSingleBase (Y 0) v := lt_of_lt_of_le (sq_pos_of_pos hα0) HH
  obtain ⟨HX, HE, HER, HEW⟩ := exitSingle_terminal_error_bounds hα hb hR hw hv
  let X := Real.sqrt ((Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2))
  change 2 < X at HX
  have HX0 : 0 < X := lt_trans (by norm_num) HX
  have HS : 0 < (Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2) :=
    Real.sqrt_pos.mp HX0
  have HXsq : X ^ 2 = (Y 0) ^ 2 + exitSingleError (Y 0) (Y 1) v (Y 2) := Real.sq_sqrt HS.le
  have Hdiff := exitSinglePhase_differential Hsq HH₀.ne' HS
  change ContDiffAt ℝ 2 f Y ∧ _ at Hdiff
  have Hdistance : |Y 0 - X| ≤ |exitSingleError (Y 0) (Y 1) v (Y 2)| := by
    have Heq : (Y 0 - X) * (Y 0 + X) = -exitSingleError (Y 0) (Y 1) v (Y 2) := by
      nlinarith only [HXsq]
    have Ha := congrArg abs Heq
    rw [abs_mul, abs_neg, abs_of_pos (by linarith only [HR, HX] : 0 < Y 0 + X)] at Ha
    nlinarith only [Ha, HR, HX, abs_nonneg (Y 0 - X)]
  refine ⟨Hdiff.1, ?_, ?_⟩
  · have HD := Hdiff.2 (Pi.single 0 1)
    simp at HD
    rw [HD]
    change |(2 * Y 0 + exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)) / (4 * X) - 1 / 2| ≤ _
    have Hid : (2 * Y 0 + exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)) / (4 * X) - 1 / 2 =
        (Y 0 - X) / (2 * X) + exitSingleErrorRadial (Y 0) (Y 1) v (Y 2) / (4 * X) := by
      field_simp; ring
    rw [Hid]
    calc
      _ ≤ |Y 0 - X| / (2 * X) + |exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)| / (4 * X) := by
        have H := abs_add_le ((Y 0 - X) / (2 * X)) (exitSingleErrorRadial (Y 0) (Y 1) v (Y 2) / (4 * X))
        simpa only [abs_div, abs_of_pos (by positivity : 0 < 2 * X),
          abs_of_pos (by positivity : 0 < 4 * X)] using H
      _ ≤ |Y 0 - X| + |exitSingleErrorRadial (Y 0) (Y 1) v (Y 2)| := by
        apply add_le_add <;> apply div_le_self (abs_nonneg _) <;> linarith only [HX]
      _ ≤ 46 * b * (v + b) / α + 900 * b * (v + b) / α ^ 2 := add_le_add (Hdistance.trans HE) HER
      _ ≤ 1024 * b * (v + b) / α ^ 2 := by
        apply (le_div_iff₀ (sq_pos_of_pos hα0)).mpr
        field_simp
        nlinarith only [mul_le_mul_of_nonneg_right hα.2 (by positivity : 0 ≤ b * (v + b)),
          mul_nonneg hb0 (add_nonneg hv0 hb0)]
  · have HD1 := Hdiff.2 (Pi.single 1 1)
    have HD2 := Hdiff.2 (Pi.single 2 1)
    simp at HD1 HD2
    rw [HD1, HD2]
    have Hwall : |2 * (Y 1 - Y 2) - 2 * v| + |-(2 * (Y 1 - Y 2)) - 2 * v| ≤ 4 * (v + b) := by
      have H3 := (abs_sub (Y 1) (Y 2)).trans hw
      calc
        _ ≤ (|2 * (Y 1 - Y 2)| + |2 * v|) + (|-(2 * (Y 1 - Y 2))| + |2 * v|) :=
          add_le_add (abs_sub _ _) (abs_sub _ _)
        _ = 4 * (|Y 1 - Y 2| + v) := by
          norm_num [abs_mul, abs_of_nonneg hv0]
          ring
        _ ≤ _ := by linarith only [H3]
    change |_ * _ / (4 * X)| + |_ * _ / (4 * X)| ≤ _
    simp only [abs_div, abs_mul, abs_of_pos HX0]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc
      _ = |exitSingleErrorWallFactor (Y 0) (Y 1) v (Y 2)| *
          (|2 * (Y 1 - Y 2) - 2 * v| + |-(2 * (Y 1 - Y 2)) - 2 * v|) / (4 * X) := by ring
      _ ≤ (24 / α) * (4 * (v + b)) := by
        have HQ := div_le_self
          (mul_nonneg (abs_nonneg (exitSingleErrorWallFactor (Y 0) (Y 1) v (Y 2)))
            (add_nonneg (abs_nonneg (2 * (Y 1 - Y 2) - 2 * v))
              (abs_nonneg (-(2 * (Y 1 - Y 2)) - 2 * v))))
          (by linarith only [HX] : 1 ≤ 4 * X)
        exact HQ.trans (mul_le_mul HEW Hwall (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity))
      _ ≤ 1024 * (v + b) / α := by
        apply (le_div_iff₀ hα0).mpr
        field_simp
        nlinarith only [hv0, hb0]

end BianchiIX
