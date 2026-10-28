import BianchiIX.Dynamics.StableHessianClockBounds

noncomputable section

namespace BianchiIX

private theorem abs_five_terms (a b c d e : ℝ) :
    |a - b + c - d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have H1 := abs_sub a b
  have H2 := abs_add_le (a - b) c
  have H3 := abs_sub (a - b + c) d
  have H4 := abs_add_le (a - b + c - d) e
  linarith only [H1, H2, H3, H4]

theorem stableBoundaryHessian_norm_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    ‖stableBoundaryHessian y v w‖ ≤ 12 * (c + 1) * ‖v‖ * ‖w‖ := by
  let K := c + 1
  let R := ‖v‖ * ‖w‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨hK, _, hm0, hmK, hm1, hm1K⟩ := stable_boundary_band hc hm
  have hKu : |y 1| ≤ K := by dsimp [K]; linarith
  have hKw : |y 2| ≤ K := by dsimp [K]; linarith
  have hKm : |y 0| ≤ K := by rwa [abs_of_nonneg hm0]
  have hKm1 : |y 0 + 1| ≤ 2 * K := by rwa [abs_of_nonneg hm1]
  have hKuw : |2 * y 1 - y 2| ≤ K := by
    have H := abs_sub (2 * y 1) (y 2)
    rw [abs_mul] at H
    norm_num only at H
    dsimp [K]
    linarith
  have hKdiff : |y 1 - y 2| ≤ K := (abs_sub _ _).trans (by dsimp [K]; linarith)
  have hp (i j : Fin 3) : |v i * w j| ≤ R := by
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i)
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j) (abs_nonneg _) (norm_nonneg _)
  have hs (i j : Fin 3) : |v i * w j + v j * w i| ≤ 2 * R :=
    (abs_add_le _ _).trans (by linarith [hp i j, hp j i])
  have ht {a A : ℝ} (ha : |a| ≤ A) (i j : Fin 3) : |a * v i * w j| ≤ A * R := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul ha (hp i j) (abs_nonneg _) ((abs_nonneg _).trans ha)
  have ht' {a A : ℝ} (ha : |a| ≤ A) (i j : Fin 3) :
      |a * (v i * w j + v j * w i)| ≤ A * (2 * R) := by
    rw [abs_mul]
    exact mul_le_mul ha (hs i j) (abs_nonneg _) ((abs_nonneg _).trans ha)
  have hscale {a A : ℝ} (ha : |a| ≤ A) {n : ℝ} (hn : 0 ≤ n) : |n * a| ≤ n * A := by
    rw [abs_mul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left ha hn
  have hKR : R ≤ K * R := by dsimp [K]; nlinarith
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i
  · have H := abs_five_terms
      ((2 * y 1 - y 2) * (v 0 * w 1 + v 1 * w 0))
      (y 1 * (v 0 * w 2 + v 2 * w 0)) (2 * y 0 * v 1 * w 1)
      ((y 0 + 1) * (v 1 * w 2 + v 2 * w 1)) (2 * v 2 * w 2)
    have H1 := ht' hKuw 0 1
    have H2 := ht' hKu 0 2
    have H3 := ht (hscale hKm (by norm_num : (0 : ℝ) ≤ 2)) 1 1
    have H4 := ht' hKm1 1 2
    have H5 := ht (by norm_num : |(2 : ℝ)| ≤ 2) 2 2
    change |stableBoundaryHessian y v w 0| ≤ _ at H
    have HB : |stableBoundaryHessian y v w 0| ≤ 12 * K * R := by
      nlinarith only [H, H1, H2, H3, H4, H5, hKR, hR]
    convert! HB using 1
    dsimp [K, R]
    ring
  · have H := abs_five_terms (-y 1 * v 0 * w 0)
      (y 0 * (v 0 * w 1 + v 1 * w 0)) (3 * y 1 * v 1 * w 1)
      (y 2 * (v 1 * w 2 + v 2 * w 1)) (-y 1 * v 2 * w 2)
    have H1 := ht (by simpa only [abs_neg] using hKu : |-y 1| ≤ K) 0 0
    have H2 := ht' hKm 0 1
    have H3 := ht (hscale hKu (by norm_num : (0 : ℝ) ≤ 3)) 1 1
    have H4 := ht' hKw 1 2
    have H5 := ht (by simpa only [abs_neg] using hKu : |-y 1| ≤ K) 2 2
    have heq : -y 1 * v 0 * w 0 - y 0 * (v 0 * w 1 + v 1 * w 0) +
        3 * y 1 * v 1 * w 1 - y 2 * (v 1 * w 2 + v 2 * w 1) + -y 1 * v 2 * w 2 =
        stableBoundaryHessian y v w 1 := by dsimp [stableBoundaryHessian]; ring
    rw [heq] at H
    have HB : |stableBoundaryHessian y v w 1| ≤ 12 * K * R := by
      nlinarith only [H, H1, H2, H3, H4, H5, hKR, hR]
    convert! HB using 1
    dsimp [K, R]
    ring
  · have H := abs_five_terms (-(v 0 * w 2 + v 2 * w 0))
      (-(2 * y 2 * v 1 * w 1)) (2 * (y 1 - y 2) * (v 1 * w 2 + v 2 * w 1))
      (2 * y 1 * v 2 * w 2) 0
    have H1 := hs 0 2
    have H2 := ht (hscale hKw (by norm_num : (0 : ℝ) ≤ 2)) 1 1
    have H3 := ht' (hscale hKdiff (by norm_num : (0 : ℝ) ≤ 2)) 1 2
    have H4 := ht (hscale hKu (by norm_num : (0 : ℝ) ≤ 2)) 2 2
    simp only [sub_neg_eq_add, add_zero, abs_neg, abs_zero] at H
    change |stableBoundaryHessian y v w 2| ≤ _ at H
    have HB : |stableBoundaryHessian y v w 2| ≤ 12 * K * R := by
      nlinarith only [H, H1, H2, H3, H4, hKR, hR]
    convert! HB using 1
    dsimp [K, R]
    ring

theorem stableTangent_split_bounds (v : StableState) :
    ‖(![v 0, 0, 0] : StableState)‖ ≤ ‖v‖ ∧
      ‖(![0, v 1, v 2] : StableState)‖ ≤ ‖![v 1, v 2]‖ ∧ ‖![v 1, v 2]‖ ≤ ‖v‖ := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 0
    · simp
    · simp
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simp
    · exact norm_le_pi_norm ![v 1, v 2] 0
    · exact norm_le_pi_norm ![v 1, v 2] 1
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 1
    · exact norm_le_pi_norm v 2

theorem stableBoundaryHessian_mixed_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    ‖stableBoundaryHessian y v w‖ ≤ (|y 1| + |y 2|) * ‖v‖ * ‖w‖ +
      12 * (c + 1) * (‖![v 1, v 2]‖ * ‖w‖ + ‖v‖ * ‖![w 1, w 2]‖) := by
  let vc : StableState := ![v 0, 0, 0]
  let vz : StableState := ![0, v 1, v 2]
  let wc : StableState := ![w 0, 0, 0]
  let wz : StableState := ![0, w 1, w 2]
  let B := fderiv ℝ (fderiv ℝ stableBoundaryField) y
  have hvsum : vc + vz = v := by ext i; fin_cases i <;> simp [vc, vz]
  have hwsum : wc + wz = w := by ext i; fin_cases i <;> simp [wc, wz]
  have hv := stableTangent_split_bounds v
  have hw' := stableTangent_split_bounds w
  have hdecomp : stableBoundaryHessian y v w = stableBoundaryHessian y vc wc +
      stableBoundaryHessian y vz w + stableBoundaryHessian y vc wz := by
    simp only [← stableBoundaryField_fderiv2]
    change B v w = B vc wc + B vz w + B vc wz
    have Hv : B v w = B vc w + B vz w := by rw [← hvsum, map_add, add_apply]
    have Hw : B vc w = B vc wc + B vc wz := by rw [← hwsum, map_add]
    rw [Hv, Hw]
    abel
  have hcc : ‖stableBoundaryHessian y vc wc‖ ≤ (|y 1| + |y 2|) * ‖v‖ * ‖w‖ := by
    have hp := mul_le_mul (norm_le_pi_norm v 0) (norm_le_pi_norm w 0) (norm_nonneg _) (norm_nonneg _)
    simp only [Real.norm_eq_abs] at hp
    have H := mul_le_mul (show |y 1| ≤ |y 1| + |y 2| by linarith [abs_nonneg (y 2)])
      hp (by positivity) (by positivity)
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · simp [stableBoundaryHessian, vc, wc]
      positivity
    · simpa [stableBoundaryHessian, vc, wc, Real.norm_eq_abs, abs_mul, mul_assoc] using H
    · simp [stableBoundaryHessian, vc, wc]
      positivity
  have hleft := (stableBoundaryHessian_norm_bound hc hm hu hw vz w).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv.2.1 (by positivity : 0 ≤ 12 * (c + 1))) (norm_nonneg w))
  have hright := (stableBoundaryHessian_norm_bound hc hm hu hw vc wz).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hv.1 (by positivity : 0 ≤ 12 * (c + 1))) hw'.2.1
      (norm_nonneg _) (by positivity))
  rw [hdecomp]
  have H := (norm_add_le (stableBoundaryHessian y vc wc + stableBoundaryHessian y vz w)
    (stableBoundaryHessian y vc wz)).trans
      (add_le_add (norm_add_le _ _) (le_refl _))
  nlinarith only [H, hcc, hleft, hright]

end BianchiIX
