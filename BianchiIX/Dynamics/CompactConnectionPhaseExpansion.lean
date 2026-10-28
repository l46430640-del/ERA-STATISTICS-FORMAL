import BianchiIX.Dynamics.CompactConnectionStrongPhase
import BianchiIX.Dynamics.CompactConnectionWeakPhase

noncomputable section

namespace BianchiIX

open Set

/-- Both parts of (B.48), with a common signed neighborhood and uniform constants. -/
theorem exists_compact_connection_phase_expansion {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y ∧
        |compactConnectionFinitePhase η Y - (Y 0 - 2 - 2 * Y 1 / Y 0)| ≤
          C * (|Y 1| + |Y 2|) ^ 2 ∧
        ∀ i : Fin 3, |fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single i 1) -
          (![1, -2 / Y 0, 0] : Fin 3 → ℝ) i| ≤ C * (|Y 1| + |Y 2|) := by
  obtain ⟨ε, hε, C, hC, HC⟩ := exists_compact_connection_finite_phase_bounds hη
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
  have hreg (Y : CoreAngleState) (hY : Y ∈ S) :=
    HC Y (hcoords hY).1 (hcoords hY).2.1 (hcoords hY).2.2
  have hdiff (Y : CoreAngleState) (hY : Y ∈ S) : DifferentiableAt ℝ (fderiv ℝ F) Y :=
    (((hreg Y hY).2.1).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hbound (Y : CoreAngleState) (hY : Y ∈ S) : ‖fderiv ℝ (fderiv ℝ F) Y‖ ≤ C := by
    have H := (hreg Y hY).2.2
    change |F Y| + ‖fderiv ℝ F Y‖ + ‖fderiv ℝ (fderiv ℝ F) Y‖ ≤ C at H
    linarith only [H, abs_nonneg (F Y), norm_nonneg (fderiv ℝ F Y)]
  have hLip {X Z : CoreAngleState} (hX : X ∈ S) (hZ : Z ∈ S) :
      ‖fderiv ℝ F X - fderiv ℝ F Z‖ ≤ C * ‖X - Z‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_Icc _ _) hZ hX
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  let Z : CoreAngleState := ![Y 0, 0, 0]
  let b := |Y 1| + |Y 2|
  have hb : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hY : Y ∈ S := hmem hk hu hw
  have hZ : Z ∈ S := hmem hk (by simpa [Z] using hε.le) (by simpa [Z] using hε.le)
  have hdist : ‖Y - Z‖ ≤ b := by
    apply (pi_norm_le_iff_of_nonneg hb).mpr
    intro i
    fin_cases i
    · change |Y 0 - Y 0| ≤ b
      simpa only [sub_self, abs_zero] using hb
    · change |Y 1 - 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_zero] using le_add_of_nonneg_right (abs_nonneg (Y 2))
    · change |Y 2 - 0| ≤ |Y 1| + |Y 2|
      simpa only [sub_zero] using le_add_of_nonneg_left (abs_nonneg (Y 1))
  have hk' : 7 / 2 ≤ Y 0 := by linarith only [hk.1]
  have haxis (i : Fin 3) : fderiv ℝ F Z (Pi.single i 1) = (![1, -2 / Y 0, 0] : Fin 3 → ℝ) i := by
    fin_cases i
    · exact compactConnectionFinitePhase_radial_reference hk.1 hη
    · exact compactConnectionFinitePhase_strong_reference hk' hη
    · exact compactConnectionFinitePhase_weak_reference hk' hη
  have hvalue : F Z = Y 0 - 2 := compactConnectionFinitePhase_reference hk' hη
  have hlin : fderiv ℝ F Z (Y - Z) = -2 * Y 1 / Y 0 := by
    have hv : Y - Z = Y 1 • Pi.single 1 1 + Y 2 • Pi.single 2 1 := by
      ext i
      fin_cases i <;> simp [Z]
    rw [hv, map_add, map_smul, map_smul, haxis 1, haxis 2]
    change Y 1 * (-2 / Y 0) + Y 2 * 0 = _
    ring
  have hrem : |F Y - F Z - fderiv ℝ F Z (Y - Z)| ≤ C * ‖Y - Z‖ ^ 2 := by
    let g := fun X : CoreAngleState => F X - fderiv ℝ F Z X
    have hseg {X : CoreAngleState} (hX : X ∈ segment ℝ Z Y) : X ∈ S :=
      (convex_Icc _ _).segment_subset hZ hY hX
    have hg (X : CoreAngleState) (hX : X ∈ segment ℝ Z Y) :
        HasFDerivAt g (fderiv ℝ F X - fderiv ℝ F Z) X :=
      (((hreg X (hseg hX)).2.1).differentiableAt (by norm_num)).hasFDerivAt.sub (fderiv ℝ F Z).hasFDerivAt
    have hbg (X : CoreAngleState) (hX : X ∈ segment ℝ Z Y) :
        ‖fderiv ℝ F X - fderiv ℝ F Z‖ ≤ C * ‖Y - Z‖ :=
      (hLip (hseg hX) hZ).trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hX) hC.le)
    have H := (convex_segment Z Y).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun X hX => (hg X hX).hasFDerivWithinAt) hbg (left_mem_segment ℝ Z Y) (right_mem_segment ℝ Z Y)
    simpa only [g, map_sub, sub_sub_sub_comm, Real.norm_eq_abs, pow_two, mul_assoc] using H
  refine ⟨(hreg Y hY).1, (hreg Y hY).2.1, ?_, ?_⟩
  · change |F Y - (Y 0 - 2 - 2 * Y 1 / Y 0)| ≤ C * b ^ 2
    calc
      _ = |F Y - F Z - fderiv ℝ F Z (Y - Z)| := by rw [hvalue, hlin]; congr 1; ring
      _ ≤ C * ‖Y - Z‖ ^ 2 := hrem
      _ ≤ C * b ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdist 2) hC.le
  · intro i
    rw [← haxis i]
    have H := (fderiv ℝ F Y - fderiv ℝ F Z).le_opNorm (Pi.single i 1)
    have H' : |fderiv ℝ F Y (Pi.single i 1) - fderiv ℝ F Z (Pi.single i 1)| ≤
        ‖fderiv ℝ F Y - fderiv ℝ F Z‖ := by
      simpa only [sub_apply, Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using H
    exact H'.trans ((hLip hY hZ).trans (mul_le_mul_of_nonneg_left hdist hC.le))

end BianchiIX
