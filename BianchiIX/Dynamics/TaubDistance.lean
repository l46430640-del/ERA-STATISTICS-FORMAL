import BianchiIX.Dynamics.AxisPermutations
import BianchiIX.Dynamics.CoreEntryDifferential
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace BianchiIX

/-- The physical Euclidean distance, distinct from the sup norm on `NormalizedState`. -/
def normalizedEuclideanDistance (x y : NormalizedState) : ℝ :=
  dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 5)) (WithLp.toLp 2 y)

def taubPoint (i : Fin 3) : NormalizedState :=
  ![![-1, 0, 0, 0, 0], ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0],
    ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]] i

theorem normalizedEuclideanDistance_nonneg (x y : NormalizedState) :
    0 ≤ normalizedEuclideanDistance x y := dist_nonneg

theorem normalizedEuclideanDistance_sq (x y : NormalizedState) :
    normalizedEuclideanDistance x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  simp [normalizedEuclideanDistance, EuclideanSpace.dist_sq_eq, Real.dist_eq]

theorem continuous_normalizedEuclideanDistance :
    Continuous (fun p : NormalizedState × NormalizedState => normalizedEuclideanDistance p.1 p.2) := by
  unfold normalizedEuclideanDistance
  fun_prop

theorem axisCycle_euclideanDistance (x y : NormalizedState) :
    normalizedEuclideanDistance (axisCycle x) (axisCycle y) = normalizedEuclideanDistance x y := by
  apply (sq_eq_sq₀ (normalizedEuclideanDistance_nonneg _ _)
    (normalizedEuclideanDistance_nonneg _ _)).mp
  rw [normalizedEuclideanDistance_sq, normalizedEuclideanDistance_sq]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [Fin.sum_univ_succ, axisCycle]
  ring_nf
  rw [hs]
  ring

theorem axisSwap_euclideanDistance (x y : NormalizedState) :
    normalizedEuclideanDistance (axisSwap x) (axisSwap y) = normalizedEuclideanDistance x y := by
  apply (sq_eq_sq₀ (normalizedEuclideanDistance_nonneg _ _)
    (normalizedEuclideanDistance_nonneg _ _)).mp
  rw [normalizedEuclideanDistance_sq, normalizedEuclideanDistance_sq]
  simp [Fin.sum_univ_succ, axisSwap]
  ring

theorem axisFrame_euclideanDistance (i : Fin 6) (x y : NormalizedState) :
    normalizedEuclideanDistance ((axisFrame i).map x) ((axisFrame i).map y) =
      normalizedEuclideanDistance x y := by
  rw [axisFrame_apply, axisFrame_apply]
  fin_cases i <;> simp [axisCycle_euclideanDistance, axisSwap_euclideanDistance]

theorem axisCycle_taubPoint (i : Fin 3) : axisCycle (taubPoint i) = taubPoint (i + 2) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i
  · change axisCycle ![-1, 0, 0, 0, 0] = ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisCycle] <;> ring
  · change axisCycle ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0] = ![-1, 0, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisCycle] <;> ring_nf
    norm_num [hs]
  · change axisCycle ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0] = ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisCycle] <;> ring_nf
    norm_num [hs]

theorem axisSwap_taubPoint (i : Fin 3) : axisSwap (taubPoint i) = taubPoint (-i) := by
  fin_cases i
  · change axisSwap ![-1, 0, 0, 0, 0] = ![-1, 0, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisSwap]
    ring
  · change axisSwap ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0] = ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisSwap]
    ring
  · change axisSwap ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0] = ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisSwap]
    ring

theorem axisFrame_taubPoint_preimage (i : Fin 6) (j : Fin 3) :
    ∃ k : Fin 3, (axisFrame i).map (taubPoint k) = taubPoint j := by
  fin_cases i
  · exact ⟨j, by simp [axisFrame_apply]⟩
  · refine ⟨j + 1, ?_⟩
    simp only [axisFrame_apply, axisCycle_taubPoint]
    fin_cases j <;> rfl
  · refine ⟨j + 2, ?_⟩
    simp only [axisFrame_apply, axisCycle_taubPoint]
    fin_cases j <;> rfl
  · refine ⟨-j, ?_⟩
    simp [axisFrame_apply, axisSwap_taubPoint]
  · refine ⟨-j + 1, ?_⟩
    simp only [axisFrame_apply, axisSwap_taubPoint, axisCycle_taubPoint]
    fin_cases j <;> rfl
  · refine ⟨-j + 2, ?_⟩
    simp only [axisFrame_apply, axisSwap_taubPoint, axisCycle_taubPoint]
    fin_cases j <;> rfl

theorem axisFrame_away_taub {x : NormalizedState} {ε : ℝ}
    (haway : ∀ j, ε ≤ normalizedEuclideanDistance x (taubPoint j)) (i : Fin 6) :
    ∀ j, ε ≤ normalizedEuclideanDistance ((axisFrame i).map x) (taubPoint j) := by
  intro j
  obtain ⟨k, hk⟩ := axisFrame_taubPoint_preimage i j
  rw [← hk, axisFrame_euclideanDistance]
  exact haway k

theorem fromProjectiveState_taubDistance_sq {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) :
    normalizedEuclideanDistance (fromProjectiveState y) (taubPoint 0) ^ 2 =
      12 * (3 + y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2) / projectiveStateDenom y ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  rw [normalizedEuclideanDistance_sq]
  simp [Fin.sum_univ_succ, fromProjectiveState, taubPoint]
  field_simp
  ring_nf
  simp only [hs]
  field_simp
  ring

theorem singleWall_taubDistance_sq (m v : ℝ) :
    normalizedEuclideanDistance (fromProjectiveState ![m, 0, v, 0]) (taubPoint 1) ^ 2 =
      3 * ((m + 1) ^ 2 + v ^ 2) / (3 + m ^ 2 + v ^ 2) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hD : 3 + m ^ 2 + v ^ 2 ≠ 0 := ne_of_gt (by positivity)
  rw [normalizedEuclideanDistance_sq]
  simp [Fin.sum_univ_succ, fromProjectiveState, taubPoint,
    projectiveStateDenom, projectiveDenom, curvature]
  field_simp
  ring_nf
  simp only [hs, show Real.sqrt 3 ^ 4 = 9 by nlinarith [sq_nonneg (Real.sqrt 3 ^ 2 - 3)]]
  ring

theorem coreRadiusEntry_taubDistance_bound {Y : CoreAngleState} (hk : 1 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ 1 / 100) (hw : 0 ≤ Y 2 ∧ Y 2 ≤ 1 / 100) :
    normalizedEuclideanDistance (fromProjectiveState (coreRadiusEntry Y)) (taubPoint 0) ^ 2 ≤
      48 / Y 0 ^ 2 := by
  let m := 1 + Real.sqrt (Y 0 ^ 2 - 1)
  let d₀ := 3 + m ^ 2 + Y 1 ^ 2 + 1 + Y 2 ^ 2
  let d := projectiveStateDenom (coreRadiusEntry Y)
  have hm : Y 0 ≤ m := by
    have H : Y 0 - 1 ≤ Real.sqrt (Y 0 ^ 2 - 1) := Real.le_sqrt_of_sq_le (by nlinarith only [hk])
    dsimp [m]
    linarith only [H]
  have hd₀ : 0 < d₀ := by dsimp [d₀]; positivity
  have hk₀ : 0 < Y 0 := lt_of_lt_of_le zero_lt_one hk
  have hkd : Y 0 ^ 2 ≤ d₀ := by
    have H := (sq_le_sq₀ hk₀.le (hk₀.le.trans hm)).mpr hm
    dsimp [d₀]
    nlinarith only [H, sq_nonneg (Y 1), sq_nonneg (Y 2)]
  have hproduct : Y 1 * Y 2 ≤ (1 / 100 : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hu.2 hw.2 hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 100)
  have hhalf : d₀ / 2 ≤ d := by
    have hd : d = d₀ - 2 * (Y 1 + Y 1 * Y 2 + Y 2) := by
      dsimp [d, d₀, m, projectiveStateDenom, coreRadiusEntry, projectiveDenom, curvature]
      ring
    rw [hd]
    dsimp [d₀]
    nlinarith only [hu.2, hw.2, hproduct, sq_nonneg m, sq_nonneg (Y 1), sq_nonneg (Y 2)]
  have hd : 0 < d := lt_of_lt_of_le (half_pos hd₀) hhalf
  have hdist : normalizedEuclideanDistance (fromProjectiveState (coreRadiusEntry Y)) (taubPoint 0) ^ 2 =
      12 * d₀ / d ^ 2 := by
    convert fromProjectiveState_taubDistance_sq hd.ne' using 1
    simp [d₀, m, coreRadiusEntry, d]
  rw [hdist]
  have hfirst : 12 * d₀ / d ^ 2 ≤ 48 / d₀ := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) hd₀).mpr
    have H := (sq_le_sq₀ (half_pos hd₀).le hd.le).mpr hhalf
    nlinarith only [H]
  exact hfirst.trans (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hk₀) hkd)

theorem coreRadiusEntry_radius_bound_of_away {Y : CoreAngleState} {ε : ℝ} (hε : 0 < ε)
    (hk : 1 ≤ Y 0) (hu : 0 ≤ Y 1 ∧ Y 1 ≤ 1 / 100) (hw : 0 ≤ Y 2 ∧ Y 2 ≤ 1 / 100)
    (haway : ε ≤ normalizedEuclideanDistance (fromProjectiveState (coreRadiusEntry Y)) (taubPoint 0)) :
    Y 0 < 8 / ε := by
  have hk₀ : 0 < Y 0 := lt_of_lt_of_le zero_lt_one hk
  have H := (le_div_iff₀ (sq_pos_of_pos hk₀)).mp (coreRadiusEntry_taubDistance_bound hk hu hw)
  have Hε := (sq_le_sq₀ hε.le (normalizedEuclideanDistance_nonneg _ _)).mpr haway
  have Hprod := mul_le_mul_of_nonneg_right Hε (sq_nonneg (Y 0))
  have Hsq : (ε * Y 0) ^ 2 ≤ 48 := by nlinarith only [H, Hprod]
  apply (lt_div_iff₀ hε).mpr
  nlinarith only [Hsq, mul_pos hε hk₀]

end BianchiIX
