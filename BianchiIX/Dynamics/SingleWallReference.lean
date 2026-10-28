import BianchiIX.Dynamics.SingleWallOrdering

noncomputable section

namespace BianchiIX

/-- A small physical wall away from Taub gives a compact reference entrance directly. -/
theorem singleWallFrame_reference {x : NormalizedState} {ε : ℝ}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hn : 0 < x 2) (hp : 1 / 2 < x 0) (hε : 0 < ε)
    (hsmall : x 2 ≤ ε ^ 2 / 8)
    (haway : ∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i)) :
    let z := (axisFrame (singleWallFrame x)).map x
    let y := toProjectiveState z
    let k := coreRadius (y 0) (y 2)
    2 ≤ k ∧ k < 4 / ε ∧ x 2 / 2 ≤ y 2 ∧ y 2 ≤ 1 / 2 ∧
      z = fromProjectiveState (referenceEntranceState k (y 2)) := by
  intro z y k
  have hA : 0 < 1 + z 0 := singleWallFrame_chart hc h3 h4 hn
  have hcon : stateConstraint z = 1 := ((axisFrame (singleWallFrame x)).constraint x).trans hc
  obtain ⟨hu, hw, hv, _, _⟩ := singleWallFrame_projective_identities hc h3 h4 hn
  change y 1 = 0 at hu
  change y 3 = 0 at hw
  change y 2 = Real.sqrt 3 * x 2 / (1 + z 0) at hv
  obtain ⟨hm, hv0, hk⟩ := singleWallFrame_projective_bounds hc h3 h4 hn hp
  change 1 < y 0 at hm
  change 0 < y 2 at hv0
  change 2 ≤ k at hk
  have hd := (axisFrame_away_taub haway (singleWallFrame x)) 0
  change ε ≤ normalizedEuclideanDistance z (taubPoint 0) at hd
  have hd2 : ε ^ 2 ≤ normalizedEuclideanDistance z (taubPoint 0) ^ 2 :=
    (sq_le_sq₀ hε.le (normalizedEuclideanDistance_nonneg _ _)).mpr hd
  have hdist : normalizedEuclideanDistance z (taubPoint 0) ^ 2 = 2 * (1 + z 0) :=
    singleWallFrame_taubDistance hc h3 h4
  have hAlo : ε ^ 2 / 2 ≤ 1 + z 0 := by linarith only [hd2, hdist]
  have hD : 3 + y 0 ^ 2 + y 2 ^ 2 = 6 / (1 + z 0) := by
    have H : projectiveStateDenom y = 6 / (1 + z 0) := projectiveDenom_of_constraint hA.ne' hcon
    simpa [projectiveStateDenom, projectiveDenom, curvature, hu, hw] using H
  have hDA := (eq_div_iff hA.ne').mp hD
  have hAhi : 1 + z 0 ≤ 2 := by
    have H : 3 ≤ 3 + y 0 ^ 2 + y 2 ^ 2 := by nlinarith only [sq_nonneg (y 0), sq_nonneg (y 2)]
    nlinarith only [mul_le_mul_of_nonneg_right H hA.le, hDA]
  have hksq : k ^ 2 = (y 0 - 1) ^ 2 + y 2 ^ 2 := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hkD : k ^ 2 < 3 + y 0 ^ 2 + y 2 ^ 2 := by nlinarith only [hksq, hm]
  have hkA : k ^ 2 * (1 + z 0) < 6 := by
    nlinarith only [mul_lt_mul_of_pos_right hkD hA, hDA]
  have hkε : k < 4 / ε := by
    apply (lt_div_iff₀ hε).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hAlo (sq_nonneg k), hkA, hk, hε]
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hrlo : 1 ≤ Real.sqrt 3 := by nlinarith only [hr, hr0]
  have hrhi : Real.sqrt 3 ≤ 2 := by nlinarith only [hr, hr0]
  have hvlo : x 2 / 2 ≤ y 2 := by
    rw [hv]
    apply (le_div_iff₀ hA).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hAhi hn.le,
      mul_le_mul_of_nonneg_right hrlo hn.le]
  have hvhi : y 2 ≤ 1 / 2 := by
    rw [hv]
    apply (div_le_iff₀ hA).mpr
    nlinarith only [hsmall, hAlo, mul_le_mul_of_nonneg_right hrhi hn.le]
  refine ⟨hk, hkε, hvlo, hvhi, ?_⟩
  have hroot : Real.sqrt (k ^ 2 - y 2 ^ 2) = y 0 - 1 := by
    rw [hksq, add_sub_cancel_right, Real.sqrt_sq (by linarith only [hm])]
  have he : referenceEntranceState k (y 2) = y := by
    ext i
    fin_cases i
    · change 1 + Real.sqrt (k ^ 2 - y 2 ^ 2) = y 0
      linarith only [hroot]
    · exact hu.symm
    · rfl
    · exact hw.symm
  rw [he]
  exact (fromProjectiveState_toProjectiveState hA.ne' hcon).symm

/-- The first upward reference crossing is the already constructed exact Einstein event. -/
theorem singleWallFrame_reference_return {x : NormalizedState} {ε : ℝ}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hn : 0 < x 2) (hp : 1 / 2 < x 0) (hε : 0 < ε)
    (hsmall : x 2 ≤ ε ^ 2 / 8)
    (haway : ∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i)) :
    let z := (axisFrame (singleWallFrame x)).map x
    let y := toProjectiveState z
    let k := coreRadius (y 0) (y 2)
    entranceReturnValid y ∧
      entranceReturnTime y = referenceShiftClock k (-referenceHeightTime k (y 2)) (-referenceHalfTime k) ∧
      entranceReturnState y = referencePulse k (-referenceHalfTime k) ∧
      normalizedMaxCurve z 0 (entranceReturnTime y) = fromProjectiveState (referencePulse k (-referenceHalfTime k)) := by
  intro z y k
  have H := singleWallFrame_reference hc h3 h4 hn hp hε hsmall haway
  change 2 ≤ k ∧ k < 4 / ε ∧ x 2 / 2 ≤ y 2 ∧ y 2 ≤ 1 / 2 ∧
    z = fromProjectiveState (referenceEntranceState k (y 2)) at H
  have hk : 7 / 4 ≤ k := by linarith only [H.1]
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨by linarith only [H.2.2.1, hn], by linarith only [H.2.2.2.1]⟩
  have hD : 0 < projectiveStateDenom (referenceEntranceState k (y 2)) := by
    simp [referenceEntranceState, projectiveStateDenom, projectiveDenom, curvature]
    positivity
  have he : y = referenceEntranceState k (y 2) := by
    change toProjectiveState z = _
    rw [H.2.2.2.2, toProjectiveState_fromProjectiveState hD.ne']
  have hr := referenceEntrance_return hk hv
  have hreg := (entranceReturn_regular (y := referenceEntranceState k (y 2)) (by
      rw [referenceEntrance_radius (by linarith only [hk]) ⟨hv.1, by linarith only [hv.2, hk]⟩]
      exact hk) (by change 1 ≤ 1 + Real.sqrt _; exact le_add_of_nonneg_right (Real.sqrt_nonneg _))
    (by dsimp [referenceEntranceState]; norm_num) hv (by dsimp [referenceEntranceState]; norm_num)).1
  refine ⟨he.symm ▸ hreg, ?_, ?_, ?_⟩
  · simpa only [← he] using hr.1
  · simpa only [← he] using hr.2
  · have horbit := referenceShiftClock_normalized_orbit k (-referenceHeightTime k (y 2)) (-referenceHalfTime k)
    rw [referencePulse_height_entry (by linarith only [hk]) ⟨hv.1, by linarith only [hk, hv.2]⟩] at horbit
    rw [H.2.2.2.2, he, hr.1]
    exact horbit.2

/-- The reference family is derived from the constrained physical entrance. -/
theorem projected_singleWall_reference {x : NormalizedState} {Δ c ε : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hnmax : x 2 ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ x 2 / 8)
    (hprod : normalizedWallProductsBound Δ x) (hcpos : 0 < c) (hε : 0 < ε)
    (hr : c ≤ rateOne (x 0) (x 1)) (hΔc : Δ ^ 2 ≤ c / 18)
    (hnc : x 2 ^ 2 ≤ c / 4) (hnε : x 2 ≤ ε ^ 2 / 32)
    (hclose : 2 * Δ ^ 2 / x 2 ≤ ε / 2)
    (haway : ∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i)) :
    ∃ a : Fin 6, ∃ k v : ℝ, 2 ≤ k ∧ k < 8 / ε ∧ x 2 / 2 ≤ v ∧ v ≤ 1 / 2 ∧
      (axisFrame a).map (singleWallProjection x) = fromProjectiveState (referenceEntranceState k v) ∧
      normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) ((axisFrame a).map x) ≤
        2 * Δ ^ 2 / x 2 := by
  let y := singleWallProjection x
  have H := normalized_singleWall_projection hc hp hnmax hΔ hprod
  have hrate : c / 2 ≤ rateOne (y 0) (y 1) := singleWall_projection_growth hc hp hnmax hΔ hprod hr hΔc
  have hycon : constraint (y 0) (y 1) (x 2) 0 0 = 1 := H.1
  have hyp : 1 / 2 < y 0 := by
    dsimp [constraint, shearSq, curvature] at hycon
    dsimp [rateOne, shearSq] at hrate
    nlinarith only [hycon, hrate, hnc, hcpos]
  have hyd : normalizedEuclideanDistance y x ≤ 2 * Δ ^ 2 / x 2 := H.2.2.2.2.2.1
  have hyaway (i : Fin 3) : ε / 2 ≤ normalizedEuclideanDistance y (taubPoint i) := by
    have Htri : normalizedEuclideanDistance x (taubPoint i) ≤
        normalizedEuclideanDistance y x + normalizedEuclideanDistance y (taubPoint i) := by
      have H' : normalizedEuclideanDistance x (taubPoint i) ≤
          normalizedEuclideanDistance x y + normalizedEuclideanDistance y (taubPoint i) := dist_triangle _ _ _
      have Hsym : normalizedEuclideanDistance x y = normalizedEuclideanDistance y x := dist_comm _ _
      rwa [Hsym] at H'
    linarith only [Htri, haway i, hyd, hclose]
  have hnε' : y 2 ≤ (ε / 2) ^ 2 / 8 := by change x 2 ≤ _; nlinarith only [hnε]
  have HR := singleWallFrame_reference H.1 H.2.2.1 H.2.2.2.1 hp.1 hyp (half_pos hε) hnε' hyaway
  let a := singleWallFrame y
  let z := (axisFrame a).map y
  let q := toProjectiveState z
  let k := coreRadius (q 0) (q 2)
  change 2 ≤ k ∧ k < 4 / (ε / 2) ∧ y 2 / 2 ≤ q 2 ∧ q 2 ≤ 1 / 2 ∧
    z = fromProjectiveState (referenceEntranceState k (q 2)) at HR
  refine ⟨a, k, q 2, HR.1, ?_, HR.2.2.1, HR.2.2.2.1, HR.2.2.2.2, ?_⟩
  · convert HR.2.1 using 1
    ring
  · rw [← HR.2.2.2.2]
    change normalizedEuclideanDistance ((axisFrame a).map y) ((axisFrame a).map x) ≤ _
    rw [axisFrame_euclideanDistance]
    exact hyd

end BianchiIX
