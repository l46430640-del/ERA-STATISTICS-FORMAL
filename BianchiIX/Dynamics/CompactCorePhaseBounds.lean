import BianchiIX.Dynamics.CompactCoreRadial

noncomputable section

namespace BianchiIX

open Set

/-- The actual compact-core map and its first derivative differ linearly from the zero-wall slice. -/
theorem exists_compact_core_linear_bounds :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      let F := coreReturnState coreRadiusReturnTime
      let Z : CoreAngleState := ![Y 0, 0, 0]
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 F Y ∧
        ‖F Y - Z‖ ≤ C * (|Y 1| + |Y 2|) ∧
        ‖fderiv ℝ F Y - fderiv ℝ F Z‖ ≤ C * (|Y 1| + |Y 2|) ∧
        ‖fderiv ℝ F Y‖ ≤ C := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_core_return_two
  let F := coreReturnState coreRadiusReturnTime
  let S : Set CoreAngleState := Icc (![2, -ε, -ε] : CoreAngleState) ![6, ε, ε]
  have hcoords {Y : CoreAngleState} (hY : Y ∈ S) :
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) ∧ |Y 1| ≤ ε ∧ |Y 2| ≤ ε :=
    ⟨⟨hY.1 0, hY.2 0⟩, abs_le.mpr ⟨hY.1 1, hY.2 1⟩,
      abs_le.mpr ⟨hY.1 2, hY.2 2⟩⟩
  have hmem {Y : CoreAngleState} (hk : 2 ≤ Y 0 ∧ Y 0 ≤ 6)
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
  have HR (Y : CoreAngleState) (hY : Y ∈ S) :=
    H Y (hcoords hY).1 (hcoords hY).2.1 (hcoords hY).2.2
  have HD (Y : CoreAngleState) (hY : Y ∈ S) : DifferentiableAt ℝ F Y :=
    (HR Y hY).2.2.1.differentiableAt (by norm_num)
  have HD₂ (Y : CoreAngleState) (hY : Y ∈ S) : DifferentiableAt ℝ (fderiv ℝ F) Y :=
    ((HR Y hY).2.2.1.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have HB (Y : CoreAngleState) (hY : Y ∈ S) :
      ‖fderiv ℝ F Y‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ F) Y‖ ≤ C := by
    have HH := (HR Y hY).2.2.2
    constructor <;> linarith only [HH, norm_nonneg (fderiv ℝ coreRadiusReturnTime Y),
      norm_nonneg (fderiv ℝ F Y), norm_nonneg (fderiv ℝ (fderiv ℝ coreRadiusReturnTime) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ F) Y)]
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw F' Z
  have hY : Y ∈ S := hmem hk hu hw
  have hZ : Z ∈ S := hmem hk (by simpa [Z] using hε.le) (by simpa [Z] using hε.le)
  have hdist : ‖Y - Z‖ ≤ |Y 1| + |Y 2| := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
    intro i
    fin_cases i
    · change |Y 0 - Y 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_self, abs_zero] using add_nonneg (abs_nonneg (Y 1)) (abs_nonneg (Y 2))
    · change |Y 1 - 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_zero] using le_add_of_nonneg_right (abs_nonneg (Y 2))
    · change |Y 2 - 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_zero] using le_add_of_nonneg_left (abs_nonneg (Y 1))
  have HV := Convex.norm_image_sub_le_of_norm_fderiv_le HD (fun X hX => (HB X hX).1)
    (convex_Icc _ _) hZ hY
  have HJ := Convex.norm_image_sub_le_of_norm_fderiv_le HD₂ (fun X hX => (HB X hX).2)
    (convex_Icc _ _) hZ hY
  have hFZ : F Z = Z := coreRadiusReturn_reference_value (by linarith only [hk.1])
  rw [hFZ] at HV
  exact ⟨(HR Y hY).1, (HR Y hY).2.2.1,
    HV.trans (mul_le_mul_of_nonneg_left hdist hC.le),
    HJ.trans (mul_le_mul_of_nonneg_left hdist hC.le), (HB Y hY).1⟩

/-- Compact-core phase errors retain the incoming amplitude and its square root along the cone. -/
theorem exists_compact_core_phase_bounds :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 ≤ Y 1 ∧ Y 1 ≤ ε) → (0 ≤ Y 2 ∧ Y 2 ≤ ε) →
      let F := coreReturnState coreRadiusReturnTime
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 F Y ∧
        |F Y 0 - Y 0| ≤ C * (Y 1 + Y 2) / Y 0 ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
          |fderiv ℝ F Y v 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_core_linear_bounds
  refine ⟨min ε (1 / 2), lt_min hε (by norm_num), 12 * C, by positivity, ?_⟩
  intro Y hk hu hw F
  obtain ⟨hvalid, hF, hval, hdiff, hnorm⟩ := H Y hk
    ((abs_of_nonneg hu.1).le.trans (hu.2.trans (min_le_left _ _)))
    ((abs_of_nonneg hw.1).le.trans (hw.2.trans (min_le_left _ _)))
  rw [abs_of_nonneg hu.1, abs_of_nonneg hw.1] at hval hdiff
  let Z : CoreAngleState := ![Y 0, 0, 0]
  let D := fderiv ℝ F Y
  let v₀ : CoreAngleState := Pi.single 0 1
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1 hw.1
  have hb1 : Y 1 + Y 2 ≤ 1 := by
    linarith only [hu.2.trans (min_le_right _ _), hw.2.trans (min_le_right _ _)]
  have hbs : Y 1 + Y 2 ≤ Real.sqrt (Y 1 + Y 2) := by
    have hs := Real.sqrt_le_one.mpr hb1
    nlinarith only [Real.sq_sqrt hb, Real.sqrt_nonneg (Y 1 + Y 2),
      mul_nonneg (Real.sqrt_nonneg (Y 1 + Y 2)) (sub_nonneg.mpr hs)]
  have hk0 : 0 < Y 0 := by linarith only [hk.1]
  have hval0 : |F Y 0 - Y 0| ≤ C * (Y 1 + Y 2) :=
    (show |F Y 0 - Y 0| ≤ ‖F Y - Z‖ from norm_le_pi_norm (F Y - Z) 0).trans hval
  refine ⟨hvalid, hF, hval0.trans ?_, ?_⟩
  · apply (le_div_iff₀ hk0).mpr
    have Hk := mul_le_mul_of_nonneg_left hk.2 (mul_nonneg hC.le hb)
    nlinarith only [Hk, mul_nonneg hC.le hb]
  · intro v hv hvu hvw
    have hcol : |D v₀ 0 - 1| ≤ C * (Y 1 + Y 2) := by
      have he : fderiv ℝ F Z v₀ = v₀ :=
        coreRadiusReturn_reference_radial_derivative (by linarith only [hk.1] : 1 < Y 0)
      have H₀ := norm_le_pi_norm ((D - fderiv ℝ F Z) v₀) 0
      have H₁ := (D - fderiv ℝ F Z).le_opNorm v₀
      have H₂ := H₀.trans H₁
      simp only [sub_apply, Pi.sub_apply, he, v₀, Pi.single_eq_same, Real.norm_eq_abs,
        Pi.norm_single, norm_one, mul_one] at H₂
      exact H₂.trans hdiff
    have hvdiff : ‖v - v₀‖ ≤ Real.sqrt (Y 1 + Y 2) := by
      apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
      intro i
      fin_cases i
      · simp [v₀, hv, Real.sqrt_nonneg]
      · simpa [v₀] using hvu.trans (Real.sqrt_le_sqrt (le_add_of_nonneg_right hw.1))
      · simpa [v₀] using hvw.trans (Real.sqrt_le_sqrt (le_add_of_nonneg_left hu.1))
    have hwall : |D (v - v₀) 0| ≤ C * Real.sqrt (Y 1 + Y 2) :=
      ((norm_le_pi_norm (D (v - v₀)) 0).trans (D.le_opNorm _)).trans
        (mul_le_mul hnorm hvdiff (norm_nonneg _) hC.le)
    have htotal : |D v 0 - 1| ≤ 2 * C * Real.sqrt (Y 1 + Y 2) := by
      have Hsplit : D v 0 - 1 = (D v₀ 0 - 1) + D (v - v₀) 0 := by rw [map_sub]; simp
      rw [Hsplit]
      have H₀ := (abs_add_le _ _).trans (add_le_add hcol hwall)
      nlinarith only [H₀, mul_le_mul_of_nonneg_left hbs hC.le]
    apply htotal.trans
    apply (le_div_iff₀ hk0).mpr
    have Hk := mul_le_mul_of_nonneg_left hk.2 (by positivity : 0 ≤ 2 * C * Real.sqrt (Y 1 + Y 2))
    nlinarith only [Hk]

end BianchiIX
