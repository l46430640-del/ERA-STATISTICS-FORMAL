import BianchiIX.Algebra.StablePhaseDerivativeBounds
import BianchiIX.Dynamics.StableCorrectedRemainderDerivatives

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

local instance : NormedAddCommGroup (StableState →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

theorem stableBoundaryProjection_derivative_decomposition {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
    let Q := fun z : StableState => stableCorrectedPhase (z 0) (z 1) (z 2)
    fderiv ℝ P y = fderiv ℝ stableCorrectedRemainder y + fderiv ℝ Q y ∧
      fderiv ℝ (fderiv ℝ P) y = fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y + fderiv ℝ (fderiv ℝ Q) y := by
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  let Q := fun z : StableState => stableCorrectedPhase (z 0) (z 1) (z 2)
  have hP : ContDiffAt ℝ 2 P y := contDiffAt_stableBoundaryProjection_two hm hu hw
  have hQ : ContDiffAt ℝ 2 Q y := contDiffAt_stableCorrectedPhase 2 (by linarith)
  have hfirst : fderiv ℝ stableCorrectedRemainder y = fderiv ℝ P y - fderiv ℝ Q y :=
    fderiv_fun_sub (hP.differentiableAt (by norm_num)) (hQ.differentiableAt (by norm_num))
  have heq : fderiv ℝ stableCorrectedRemainder =ᶠ[𝓝 y] (fun z => fderiv ℝ P z - fderiv ℝ Q z) := by
    filter_upwards [hP.eventually (by norm_num), hQ.eventually (by norm_num)] with z hp hq
    exact fderiv_fun_sub (hp.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num))
  have hsecond : fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y =
      fderiv ℝ (fderiv ℝ P) y - fderiv ℝ (fderiv ℝ Q) y := by
    rw [heq.fderiv_eq]
    exact fderiv_fun_sub
      ((hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num))
      ((hQ.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num))
  exact ⟨(sub_eq_iff_eq_add).mp hfirst.symm, (sub_eq_iff_eq_add).mp hsecond.symm⟩

theorem exists_stableBoundaryProjection_refined_derivatives :
    ∃ C > (0 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      let L := y 0 + 1
      let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
      (∀ v, v 1 = 0 → v 2 = 0 → |fderiv ℝ P y v - v 0| ≤ C / L ^ 2 * b ^ 2 * ‖v‖) ∧
      (∀ v, v 0 = 0 → |fderiv ℝ P y v| ≤ C / L * b * ‖v‖) ∧
      (∀ v r, v 1 = 0 → v 2 = 0 → r 1 = 0 → r 2 = 0 →
        |fderiv ℝ (fderiv ℝ P) y v r| ≤ C / L ^ 3 * b ^ 2 * ‖v‖ * ‖r‖) ∧
      (∀ v r, v 1 = 0 → v 2 = 0 → r 0 = 0 →
        |fderiv ℝ (fderiv ℝ P) y v r| ≤ C / L ^ 2 * b * ‖v‖ * ‖r‖) ∧
      (∀ v r, v 0 = 0 → r 0 = 0 →
        |fderiv ℝ (fderiv ℝ P) y v r| ≤ C / L * ‖v‖ * ‖r‖) := by
  obtain ⟨C, hC, HC⟩ := exists_stableCorrectedRemainder_amplitude_bounds
  refine ⟨C + 40, by positivity, ?_⟩
  intro y hm hu hw
  obtain ⟨hr1, hrM, hr2, hrMz, hrMM⟩ := HC y hm hu hw
  obtain ⟨hpM, hpz, hpMM, hpMz, hpzz⟩ := stableCorrectedPhase_directional_bounds hm
  obtain ⟨hd1, hd2⟩ := stableBoundaryProjection_derivative_decomposition hm hu hw
  let b := |y 1| + |y 2|
  let L := y 0 + 1
  let Q := fun z : StableState => stableCorrectedPhase (z 0) (z 1) (z 2)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := by linarith
  have hsmall (p q n : ℕ) (hpq : q ≤ p) (hn : n ≤ 3) :
      C / L ^ 3 * b ^ p ≤ C / L ^ n * b ^ q :=
    mul_le_mul (div_le_div_of_nonneg_left hC.le (pow_pos hL n) (pow_le_pow_right₀ hL1 hn))
      (pow_le_pow_of_le_one hb hb1 hpq) (by positivity) (by positivity)
  dsimp only
  rw [hd1, hd2]
  simp only [add_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv1 hv2
    have R := hrM v hv1 hv2
    have S := hpM v hv1 hv2
    have B := mul_le_mul_of_nonneg_right (hsmall 4 2 2 (by norm_num) (by norm_num)) (norm_nonneg v)
    have H := abs_add_le (fderiv ℝ stableCorrectedRemainder y v) (fderiv ℝ Q y v - v 0)
    have hpos : 0 ≤ (1 / L ^ 2) * b ^ 2 * ‖v‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, one_mul] at R S B hpos ⊢
    rw [add_sub_assoc]
    nlinarith only [R, S, B, H, hpos]
  · intro v hv0
    have R := hr1 v
    have S := hpz v hv0
    have B := mul_le_mul_of_nonneg_right (hsmall 3 1 1 (by norm_num) (by norm_num)) (norm_nonneg v)
    have H := abs_add_le (fderiv ℝ stableCorrectedRemainder y v) (fderiv ℝ Q y v)
    have hpos : 0 ≤ (1 / L) * b * ‖v‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, pow_one, one_mul] at R S B hpos ⊢
    nlinarith only [R, S, B, H, hpos]
  · intro v r hv1 hv2 hr1' hr2'
    have R := hrMM v r hv1 hv2 hr1' hr2'
    have S := hpMM v r hv1 hv2 hr1' hr2'
    have B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hsmall 4 2 3 (by norm_num) (le_refl 3)) (norm_nonneg v)) (norm_nonneg r)
    have H := abs_add_le (fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v r) (fderiv ℝ (fderiv ℝ Q) y v r)
    have hpos : 0 ≤ (1 / L ^ 3) * b ^ 2 * ‖v‖ * ‖r‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, one_mul] at R S B hpos ⊢
    nlinarith only [R, S, B, H, hpos]
  · intro v r hv1 hv2 hr0
    have R := hrMz v r hv1 hv2
    have S := hpMz v r hv1 hv2 hr0
    have B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hsmall 3 1 2 (by norm_num) (by norm_num)) (norm_nonneg v)) (norm_nonneg r)
    have H := abs_add_le (fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v r) (fderiv ℝ (fderiv ℝ Q) y v r)
    have hpos : 0 ≤ (1 / L ^ 2) * b * ‖v‖ * ‖r‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, pow_one, one_mul] at R S B hpos ⊢
    nlinarith only [R, S, B, H, hpos]
  · intro v r hv0 hr0
    have R := hr2 v r
    have S := hpzz v r hv0 hr0
    have B := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hsmall 2 0 1 (by norm_num) (by norm_num)) (norm_nonneg v)) (norm_nonneg r)
    have H := abs_add_le (fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v r) (fderiv ℝ (fderiv ℝ Q) y v r)
    have hpos : 0 ≤ (1 / L) * ‖v‖ * ‖r‖ := by positivity
    dsimp only [L, b, Q] at B H hpos
    simp only [div_eq_mul_inv, pow_one, pow_zero, mul_one, one_mul] at R S B hpos ⊢
    nlinarith only [R, S, B, H, hpos]

end BianchiIX
