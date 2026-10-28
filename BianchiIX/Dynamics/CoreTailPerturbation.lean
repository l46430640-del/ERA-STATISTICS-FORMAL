import BianchiIX.Dynamics.CoreTailBoundary
import BianchiIX.Algebra.PhaseBoundaryStability

noncomputable section

namespace BianchiIX

open Set

def coreTailReflectedRadius (η : ℝ) (Y : CoreAngleState) : ℝ :=
  coreRadius (projectiveReflection (coreTailState η Y) 0) (projectiveReflection (coreTailState η Y) 2)

theorem coreTailReflectedRadius_eq (η : ℝ) (Y : CoreAngleState) :
    coreTailReflectedRadius η Y = phaseNorm (-coreTailState η Y 0 - 1) (coreTailState η Y 3) := rfl

theorem contDiffAt_coreTailReflectedRadius (n : WithTop ℕ∞) {η : ℝ} {Y : CoreAngleState}
    (hP : ContDiffAt ℝ n (coreTailState η) Y) (hm : 1 < -coreTailState η Y 0) :
    ContDiffAt ℝ n (coreTailReflectedRadius η) Y := by
  have ha : ContDiffAt ℝ n (fun Z => -coreTailState η Z 0 - 1) Y :=
    (contDiffAt_pi.mp hP 0).neg.sub contDiffAt_const
  have hb : ContDiffAt ℝ n (fun Z => coreTailState η Z 3) Y := contDiffAt_pi.mp hP 3
  have hsq : (-coreTailState η Y 0 - 1) ^ 2 + coreTailState η Y 3 ^ 2 ≠ 0 := by
    have hp : 0 < -coreTailState η Y 0 - 1 := by linarith only [hm]
    exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hp) (sq_nonneg _))
  exact ((ha.pow 2).add (hb.pow 2)).sqrt hsq

/-- The uniform finite-tail derivative bound controls every signed wall perturbation. -/
theorem exists_compact_tail_state_perturbation {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧ ContDiffAt ℝ 2 (coreTailState η) Y ∧
        ‖coreTailState η Y - (![1 - Real.sqrt (Y 0 ^ 2 - η ^ 2), 0, η, 0] : ProjectiveState)‖ ≤
          C * (|Y 1| + |Y 2|) := by
  obtain ⟨ε, hε, C, hC, Htail⟩ := exists_compact_connection_tail hη
  let S : Set CoreAngleState := Icc (![31 / 8, -ε, -ε] : CoreAngleState) ![6, ε, ε]
  have hcoords {Y : CoreAngleState} (hY : Y ∈ S) :
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) ∧ |Y 1| ≤ ε ∧ |Y 2| ≤ ε :=
    ⟨⟨hY.1 0, hY.2 0⟩, abs_le.mpr ⟨hY.1 1, hY.2 1⟩, abs_le.mpr ⟨hY.1 2, hY.2 2⟩⟩
  have hdiff (Y : CoreAngleState) (hY : Y ∈ S) : DifferentiableAt ℝ (coreTailState η) Y :=
    (Htail Y (hcoords hY).1 (hcoords hY).2.1 (hcoords hY).2.2).2.2.1.differentiableAt (by norm_num)
  have hbound (Y : CoreAngleState) (hY : Y ∈ S) : ‖fderiv ℝ (coreTailState η) Y‖ ≤ C := by
    have H := (Htail Y (hcoords hY).1 (hcoords hY).2.1 (hcoords hY).2.2).2.2.2
    linarith only [H, abs_nonneg (coreTailTime η Y), norm_nonneg (coreTailState η Y),
      norm_nonneg (fderiv ℝ (coreTailTime η) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (coreTailTime η)) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (coreTailState η)) Y)]
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  have hY : Y ∈ S := by
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
  have hbase : (![Y 0, 0, 0] : CoreAngleState) ∈ S := by
    constructor
    · intro i
      fin_cases i
      · exact hk.1
      · exact neg_nonpos.mpr hε.le
      · exact neg_nonpos.mpr hε.le
    · intro i
      fin_cases i
      · exact hk.2
      · exact hε.le
      · exact hε.le
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_Icc _ _) hbase hY
  have hnorm : ‖Y - (![Y 0, 0, 0] : CoreAngleState)‖ ≤ |Y 1| + |Y 2| := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
    intro i
    fin_cases i
    · change |Y 0 - Y 0| ≤ |Y 1| + |Y 2|
      rw [sub_self, abs_zero]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    · change |Y 1 - 0| ≤ |Y 1| + |Y 2|
      rw [sub_zero]
      exact le_add_of_nonneg_right (abs_nonneg (Y 2))
    · change |Y 2 - 0| ≤ |Y 1| + |Y 2|
      rw [sub_zero]
      exact le_add_of_nonneg_left (abs_nonneg (Y 1))
  have href := (coreTail_reference_regular (k := Y 0) (by linarith only [hk.1])
    ⟨hη.1, by linarith only [hη.2]⟩).2.1
  rw [href] at H
  have HY := Htail Y hk hu hw
  exact ⟨HY.1, HY.2.1, HY.2.2.1, H.trans (mul_le_mul_of_nonneg_left hnorm hC.le)⟩

/-- B.46 for the actual nonzero-wall tail, together with the state error controlling its branch. -/
theorem exists_compact_tail_phase_perturbation {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧ ContDiffAt ℝ 2 (coreTailState η) Y ∧
        |coreTailReflectedRadius η Y - (Real.sqrt (Y 0 ^ 2 - η ^ 2) - 2)| ≤ C * (|Y 1| + |Y 2|) ∧
        |(-coreTailState η Y 0 - 1) - (Real.sqrt (Y 0 ^ 2 - η ^ 2) - 2)| ≤ C * (|Y 1| + |Y 2|) := by
  obtain ⟨ε, hε, C, hC, Htail⟩ := exists_compact_tail_state_perturbation hη
  refine ⟨ε, hε, 2 * C, by positivity, ?_⟩
  intro Y hk hu hw
  have HY := Htail Y hk hu hw
  let s := Real.sqrt (Y 0 ^ 2 - η ^ 2) - 2
  have hs : 0 ≤ s := by
    have H := (compact_connection_boundary_radius_bounds hk hη).1
    have hηsq := pow_le_pow_left₀ hη.1.le hη.2 2
    dsimp only [s]
    nlinarith only [H, hηsq]
  have hcoord (i : Fin 4) := (norm_le_pi_norm
    (coreTailState η Y - (![1 - Real.sqrt (Y 0 ^ 2 - η ^ 2), 0, η, 0] : ProjectiveState)) i).trans HY.2.2.2
  have hm : |(-coreTailState η Y 0 - 1) - s| ≤ C * (|Y 1| + |Y 2|) := by
    have heq : (-coreTailState η Y 0 - 1) - s =
        -(coreTailState η Y 0 - (1 - Real.sqrt (Y 0 ^ 2 - η ^ 2))) := by dsimp only [s]; ring
    rw [heq, abs_neg]
    exact hcoord 0
  have hwout : |coreTailState η Y 3| ≤ C * (|Y 1| + |Y 2|) := by simpa using hcoord 3
  have hphase := phaseNorm_boundary_error (a := -coreTailState η Y 0 - 1)
    (b := coreTailState η Y 3) hs
  refine ⟨HY.1, HY.2.1, HY.2.2.1, ?_, ?_⟩
  · rw [coreTailReflectedRadius_eq]
    change |phaseNorm (-coreTailState η Y 0 - 1) (coreTailState η Y 3) - s| ≤ _
    linarith only [hphase, hm, hwout]
  · exact hm.trans (by nlinarith only [mul_nonneg hC.le (add_nonneg (abs_nonneg (Y 1)) (abs_nonneg (Y 2)))])

end BianchiIX
