import BianchiIX.Dynamics.EntranceProjectionEstimates

noncomputable section

namespace BianchiIX

/-- The cancellation in the phase column gains two powers of the entrance parameter. -/
theorem exists_entranceWeakNumerator_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      let b := y 1 + y 3
      |entranceWeakNumerator y| ≤ C * b ^ 2 ∧
      |fderiv ℝ entranceWeakNumerator y (Pi.single 0 1)| ≤ C * b ^ 2 / k ^ 2 ∧
      |fderiv ℝ entranceWeakNumerator y (Pi.single 1 1)| ≤ C * b ∧
      |fderiv ℝ entranceWeakNumerator y (Pi.single 3 1)| ≤ C * b := by
  obtain ⟨C, hC, HC⟩ := exists_entranceProjection_estimates
  refine ⟨8 * (C + 1), by positivity, ?_⟩
  intro k y hk hy
  let b := y 1 + y 3
  have hb : 0 ≤ b := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hval, hM, hU, hW, hMM, hMU, hMW⟩ := HC k y hk hy
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hchi0 : 0 ≤ entranceStablePhase y - 1 := by linarith [hchi.1]
  have hchi2 : entranceStablePhase y - 1 ≤ 2 * k := by linarith [hchi.2]
  have hPM0 : 0 ≤ entranceStablePartial y 0 := by linarith [hPM.1]
  have hPM2 : entranceStablePartial y 0 ≤ 2 := by linarith [hPM.2]
  have hchi_mul (a q : ℝ) (ha : |a| ≤ q) : |(entranceStablePhase y - 1) * a| ≤ 2 * k * q := by
    rw [abs_mul, abs_of_nonneg hchi0]
    exact mul_le_mul hchi2 ha (abs_nonneg _) (by positivity)
  have hPM_mul (a q : ℝ) (ha : |a| ≤ q) : |entranceStablePartial y 0 * a| ≤ 2 * q := by
    rw [abs_mul, abs_of_nonneg hPM0]
    exact mul_le_mul hPM2 ha (abs_nonneg _) (by norm_num)
  have hdiv (q : ℝ) (hq : 0 ≤ q) : C * q / k ≤ C * q := div_le_self (by positivity) hk1
  have hcancel (q : ℝ) : 2 * k * (C * q / k ^ 2) = 2 * (C * q / k) := by
    field_simp
  have hcancel2 : 2 * k * (C * b ^ 2 / k ^ 3) = 2 * (C * b ^ 2 / k ^ 2) := by
    field_simp
  have hquad : |y 1 * (y 3 - y 1)| ≤ b ^ 2 := by
    have hdiff : |y 3 - y 1| ≤ b := by
      calc
        _ ≤ |y 3| + |y 1| := abs_sub _ _
        _ = b := by rw [abs_of_nonneg hy.2.2.1.1, abs_of_nonneg hy.2.2.2.2.1]; dsimp [b]; ring
    rw [abs_mul, abs_of_nonneg hy.2.2.1.1, pow_two]
    exact mul_le_mul (by dsimp [b]; linarith [hy.2.2.2.2.1]) hdiff (abs_nonneg _) hb
  have hn : |entranceWeakNumerator y| ≤ (3 * C + 1) * b ^ 2 := by
    have he : entranceWeakNumerator y = -(entranceStablePhase y - y 0) - y 1 * (y 3 - y 1) -
        (entranceStablePhase y - 1) * (entranceStablePartial y 0 - 1) := by
      unfold entranceWeakNumerator
      ring
    rw [he]
    calc
      _ ≤ |entranceStablePhase y - y 0| + |y 1 * (y 3 - y 1)| +
          |(entranceStablePhase y - 1) * (entranceStablePartial y 0 - 1)| := by
        calc
          _ ≤ |-(entranceStablePhase y - y 0)| + |y 1 * (y 3 - y 1)| +
              |(entranceStablePhase y - 1) * (entranceStablePartial y 0 - 1)| :=
            (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
          _ = _ := by rw [abs_neg]
      _ ≤ C * b ^ 2 / k + b ^ 2 + 2 * k * (C * b ^ 2 / k ^ 2) :=
        add_le_add (add_le_add hval hquad) (hchi_mul _ _ hM)
      _ = 3 * (C * b ^ 2 / k) + b ^ 2 := by rw [hcancel]; ring
      _ ≤ 3 * (C * b ^ 2) + b ^ 2 := add_le_add (mul_le_mul_of_nonneg_left (hdiv _ (sq_nonneg b)) (by norm_num)) le_rfl
      _ = _ := by ring
  have hsquare : |1 - entranceStablePartial y 0 ^ 2| ≤ 3 * (C * b ^ 2 / k ^ 2) := by
    calc
      _ = |entranceStablePartial y 0 - 1| * (entranceStablePartial y 0 + 1) := by
        rw [show 1 - entranceStablePartial y 0 ^ 2 =
          -(entranceStablePartial y 0 - 1) * (entranceStablePartial y 0 + 1) by ring,
          abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ entranceStablePartial y 0 + 1)]
      _ ≤ (C * b ^ 2 / k ^ 2) * 3 := mul_le_mul hM (by linarith) (by linarith) (by positivity)
      _ = _ := by ring
  obtain ⟨h0, h1, h3⟩ := entranceWeakNumerator_partials hm hu hw
  have hnM : |fderiv ℝ entranceWeakNumerator y (Pi.single 0 1)| ≤ 5 * C * b ^ 2 / k ^ 2 := by
    rw [h0]
    calc
      _ ≤ |1 - entranceStablePartial y 0 ^ 2| + |(entranceStablePhase y - 1) *
        fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 0 1)| := abs_sub _ _
      _ ≤ 3 * (C * b ^ 2 / k ^ 2) + 2 * k * (C * b ^ 2 / k ^ 3) :=
        add_le_add hsquare (hchi_mul _ _ hMM)
      _ = _ := by rw [hcancel2]; ring
  have hlin : |2 * y 1 - y 3| ≤ 2 * b := by
    calc
      _ ≤ |2 * y 1| + |y 3| := abs_sub _ _
      _ ≤ 2 * b := by rw [abs_of_nonneg (mul_nonneg (by norm_num) hy.2.2.1.1), abs_of_nonneg hy.2.2.2.2.1]; dsimp [b]; linarith [hy.2.2.2.2.1]
  have hwall (a s t : ℝ) (ha : |a| ≤ 2 * b) (hs : |s| ≤ C * b / k)
      (ht : |t| ≤ C * b / k ^ 2) :
      |a - entranceStablePartial y 0 * s - (entranceStablePhase y - 1) * t| ≤ (4 * C + 2) * b := by
    calc
      _ ≤ |a| + |entranceStablePartial y 0 * s| + |(entranceStablePhase y - 1) * t| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 2 * b + 2 * (C * b / k) + 2 * k * (C * b / k ^ 2) :=
        add_le_add (add_le_add ha (hPM_mul _ _ hs)) (hchi_mul _ _ ht)
      _ = 2 * b + 4 * (C * b / k) := by rw [hcancel]; ring
      _ ≤ 2 * b + 4 * (C * b) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hdiv b hb) (by norm_num))
      _ = _ := by ring
  have hnU := hwall _ _ _ hlin hU hMU
  have hnW := hwall (-y 1) _ _ (by rw [abs_neg, abs_of_nonneg hy.2.2.1.1]; dsimp [b]; linarith [hy.2.2.1.1, hy.2.2.2.2.1]) hW hMW
  dsimp only
  rw [h1, h3]
  refine ⟨hn.trans ?_, hnM.trans ?_, hnU.trans ?_, hnW.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith : 3 * C + 1 ≤ 8 * (C + 1)) (sq_nonneg b)
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 5 * C ≤ 8 * (C + 1)) (sq_nonneg b)) (sq_nonneg k)
  · exact mul_le_mul_of_nonneg_right (by linarith : 4 * C + 2 ≤ 8 * (C + 1)) hb
  · exact mul_le_mul_of_nonneg_right (by linarith : 4 * C + 2 ≤ 8 * (C + 1)) hb

end BianchiIX
