import BianchiIX.Dynamics.StableQuadraticExpansion

noncomputable section

namespace BianchiIX

local instance stableQuadraticRemainderOperatorGroup : NormedAddCommGroup (StableState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance stableQuadraticRemainderOperatorSpace : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

theorem exists_stableQuadraticRemainder_bounds :
    ∃ C > (0 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      let L := y 0 + 1
      ContDiffAt ℝ 2 stableQuadraticRemainder y ∧
      |stableQuadraticRemainder y| ≤ C / L ^ 3 * b ^ 4 ∧
      (∀ v, v 1 = 0 → v 2 = 0 → |fderiv ℝ stableQuadraticRemainder y v| ≤ C / L ^ 3 * b ^ 4 * ‖v‖) ∧
      (∀ v, v 0 = 0 → |fderiv ℝ stableQuadraticRemainder y v| ≤ C / L ^ 3 * b ^ 3 * ‖v‖) ∧
      (∀ v r, v 1 = 0 → v 2 = 0 → r 1 = 0 → r 2 = 0 →
        |fderiv ℝ (fderiv ℝ stableQuadraticRemainder) y v r| ≤ C / L ^ 3 * b ^ 4 * ‖v‖ * ‖r‖) ∧
      (∀ v r, v 1 = 0 → v 2 = 0 → r 0 = 0 →
        |fderiv ℝ (fderiv ℝ stableQuadraticRemainder) y v r| ≤ C / L ^ 3 * b ^ 3 * ‖v‖ * ‖r‖) ∧
      (∀ v r, v 0 = 0 → r 0 = 0 →
        |fderiv ℝ (fderiv ℝ stableQuadraticRemainder) y v r| ≤ C / L ^ 3 * b ^ 2 * ‖v‖ * ‖r‖) := by
  obtain ⟨A, hA, HA⟩ := exists_stableCorrectedRemainder_weighted_bounds
  obtain ⟨C, hC, HC⟩ := exists_stableCorrectedRemainder_amplitude_bounds
  refine ⟨A + C + 4, by positivity, ?_⟩
  intro y hm hu hw
  obtain ⟨_, hr0, _, _⟩ := HA y hm hu hw
  obtain ⟨hr1, hrM, hr2, hrMz, hrMM⟩ := HC y hm hu hw
  obtain ⟨he0, heM, hez, heMM, heMz, hezz⟩ := stableWeakRemainder_directional_bounds (y := y) (by linarith)
  obtain ⟨hreg, hd1, hd2⟩ := stableQuadraticRemainder_derivatives hm hu hw
  let b := |y 1| + |y 2|
  let L := y 0 + 1
  let E := fun z : StableState => stableWeakRemainder (z 0) (z 2)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := by linarith
  have hscale (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 3 ≤ n) : a / L ^ n ≤ a / L ^ 3 :=
    div_le_div_of_nonneg_left ha (pow_pos hL 3) (pow_le_pow_right₀ hL1 hn)
  have hsum {x z q : ℝ} (hq : 0 ≤ q) (hx : |x| ≤ C * q) (hz : |z| ≤ 3 * q) :
      |x + z| ≤ (A + C + 4) * q := by
    nlinarith only [abs_add_le x z, hx, hz, hq, mul_nonneg hA.le hq]
  dsimp only
  refine ⟨hreg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stableQuadraticRemainder_decomposition]
    have hU : |y 1| ≤ b := le_add_of_nonneg_right (abs_nonneg (y 2))
    have B := mul_le_mul_of_nonneg_left hU (show 0 ≤ A / L ^ 3 * b ^ 3 by positivity)
    have H := abs_add_le (stableCorrectedRemainder y) (E y)
    have hpos : 0 ≤ b ^ 4 / L ^ 3 := by positivity
    have hposC := mul_nonneg hC.le hpos
    dsimp only [L, b, E] at B H hpos hposC
    simp only [div_eq_mul_inv] at B hr0 he0 hpos hposC ⊢
    nlinarith only [hr0, B, he0, H, hpos, hposC]
  · intro v hv1 hv2
    rw [hd1, add_apply]
    refine (hsum (q := b ^ 4 / L ^ 3 * ‖v‖) (by positivity) ?_ ?_).trans_eq ?_
    · convert hrM v hv1 hv2 using 1
      dsimp [L, b]
      ring
    · have H := (heM v hv1 hv2).trans
        (mul_le_mul_of_nonneg_right (hscale (b ^ 4) (by positivity) 4 (by norm_num)) (norm_nonneg v))
      nlinarith only [H, show 0 ≤ b ^ 4 / L ^ 3 * ‖v‖ by positivity]
    · dsimp [L, b]
      ring
  · intro v hv0
    rw [hd1, add_apply]
    refine (hsum (q := b ^ 3 / L ^ 3 * ‖v‖) (by positivity) ?_ ?_).trans_eq ?_
    · convert hr1 v using 1
      dsimp [L, b]
      ring
    · have H := hez v hv0
      change |fderiv ℝ E y v| ≤ b ^ 3 / L ^ 3 * ‖v‖ at H
      nlinarith only [H, show 0 ≤ b ^ 3 / L ^ 3 * ‖v‖ by positivity]
    · dsimp [L, b]
      ring
  · intro v r hv1 hv2 hr1' hr2'
    rw [hd2, add_apply, add_apply]
    refine (hsum (q := b ^ 4 / L ^ 3 * ‖v‖ * ‖r‖) (by positivity) ?_ ?_).trans_eq ?_
    · convert hrMM v r hv1 hv2 hr1' hr2' using 1
      dsimp [L, b]
      ring
    · have H := (heMM v r hv1 hv2 hr1' hr2').trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (hscale (3 * b ^ 4) (by positivity) 5 (by norm_num)) (norm_nonneg v)) (norm_nonneg r))
      calc
        _ ≤ 3 * b ^ 4 / L ^ 3 * ‖v‖ * ‖r‖ := H
        _ = _ := by ring
    · dsimp [L, b]
      ring
  · intro v r hv1 hv2 hr0'
    rw [hd2, add_apply, add_apply]
    refine (hsum (q := b ^ 3 / L ^ 3 * ‖v‖ * ‖r‖) (by positivity) ?_ ?_).trans_eq ?_
    · convert hrMz v r hv1 hv2 using 1
      dsimp [L, b]
      ring
    · have H := (heMz v r hv1 hv2 hr0').trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (hscale (3 * b ^ 3) (by positivity) 4 (by norm_num)) (norm_nonneg v)) (norm_nonneg r))
      calc
        _ ≤ 3 * b ^ 3 / L ^ 3 * ‖v‖ * ‖r‖ := H
        _ = _ := by ring
    · dsimp [L, b]
      ring
  · intro v r hv0 hr0'
    rw [hd2, add_apply, add_apply]
    refine (hsum (q := b ^ 2 / L ^ 3 * ‖v‖ * ‖r‖) (by positivity) ?_ ?_).trans_eq ?_
    · convert hr2 v r using 1
      dsimp [L, b]
      ring
    · convert hezz v r hv0 hr0' using 1
      dsimp [L, b]
      ring
    · dsimp [L, b]
      ring

end BianchiIX
