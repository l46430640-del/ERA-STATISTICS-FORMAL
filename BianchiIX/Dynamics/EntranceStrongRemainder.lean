import BianchiIX.Dynamics.EntranceProjectionEstimates

noncomputable section

namespace BianchiIX

theorem contDiffAt_entranceStrongBracket_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 1 entranceStrongBracket y := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hM := contDiffAt_entranceStablePartial_one hm hu hw 0
  unfold entranceStrongBracket
  fun_prop

theorem contDiffAt_entranceStrongRemainder_one {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 1 entranceStrongRemainder y := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hpartial := contDiffAt_entranceStablePartial_one hm hu hw
  unfold entranceStrongRemainder
  fun_prop

/-- Differentiation of the factored remainder uses only second derivatives of the projection. -/
theorem entranceStrongRemainder_phase_derivative {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    let Q := fderiv ℝ (fderiv ℝ entranceStablePhase) y
    fderiv ℝ entranceStrongRemainder y (Pi.single 0 1) =
      entranceStablePartial y 0 * (entranceStrongBracket y +
        y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) - y 2 * entranceStablePartial y 1 / 2) +
      (entranceStablePhase y - 1) * (-(y 0 - 1) * Q (Pi.single 0 1) (Pi.single 0 1) +
        y 3 * (Q (Pi.single 0 1) (Pi.single 1 1) - Q (Pi.single 0 1) (Pi.single 3 1)) -
        y 2 * Q (Pi.single 0 1) (Pi.single 1 1) / 2) := by
  have hP := (contDiffAt_entranceStablePhase_two hm hu hw).differentiableAt (by norm_num)
  have hF := (contDiffAt_entranceStrongBracket_one hm hu hw).differentiableAt (by norm_num)
  have hp (i : Fin 4) := ((contDiffAt_entranceStablePartial_one hm hu hw i).differentiableAt (by norm_num)).hasFDerivAt
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i y
  have H := (hP.hasFDerivAt.sub_const 1).mul
    ((hF.hasFDerivAt.add ((hd 3).mul ((hp 1).sub (hp 3)))).sub (((hd 2).mul (hp 1)).mul_const (1 / 2)))
  have heq : entranceStrongRemainder = (fun z => (entranceStablePhase z - 1) *
      (entranceStrongBracket z + z 3 * (entranceStablePartial z 1 - entranceStablePartial z 3) -
        z 2 * entranceStablePartial z 1 * (1 / 2))) := by
    funext z
    rw [entranceStrongRemainder_bracket]
    ring
  change HasFDerivAt (fun z => (entranceStablePhase z - 1) *
    (entranceStrongBracket z + z 3 * (entranceStablePartial z 1 - entranceStablePartial z 3) -
      z 2 * entranceStablePartial z 1 * (1 / 2))) _ y at H
  rw [heq, H.fderiv]
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
    Pi.single_eq_of_ne (by decide : (2 : Fin 4) ≠ 0), Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 0),
    mul_zero, add_zero, entranceStablePartial_fderiv hm hu hw,
    entranceStrongBracket_phase_cancellation hm hu hw]
  unfold entranceStablePartial
  ring

set_option maxHeartbeats 400000 in
theorem exists_entranceStrongRemainder_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      let b := y 1 + y 3
      |entranceStrongBracket y| ≤ C * b ^ 2 / k ∧
      |entranceStrongRemainder y| ≤ C * (y 2 * b + b ^ 2) ∧
      |fderiv ℝ entranceStrongRemainder y (Pi.single 0 1)| ≤ C * (y 2 * b + b ^ 2) / k := by
  obtain ⟨C, hC, HC⟩ := exists_entranceProjection_estimates
  refine ⟨32 * C, by positivity, ?_⟩
  intro k y hk hy
  let b := y 1 + y 3
  let s := y 2 * b + b ^ 2
  have hb : 0 ≤ b := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hV := hy.2.2.2.1.1
  have hW := hy.2.2.2.2.1
  have hWb : y 3 ≤ b := by dsimp [b]; linarith [hy.2.2.1.1]
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hk0 : 0 < k := by linarith
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hW]; linarith [hy.2.2.2.2.2]
  obtain ⟨hp, hpM, hpU, hpW, hMM, hMU, hMW⟩ := HC k y hk hy
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hchi0 : 0 ≤ entranceStablePhase y - 1 := by linarith [hchi.1]
  have hchi2 : entranceStablePhase y - 1 ≤ 2 * k := by linarith [hchi.2]
  have hm0 : 0 ≤ y 0 - 1 := by linarith
  have hm2 : y 0 - 1 ≤ 2 * k := by linarith [(entranceRegion_phase hk hy).2]
  have hPM0 : 0 ≤ entranceStablePartial y 0 := by linarith [hPM.1]
  have hPM2 : entranceStablePartial y 0 ≤ 2 := by linarith [hPM.2]
  have hmul (a t q : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2 * k) (ht : |t| ≤ q) : |a * t| ≤ 2 * k * q := by
    rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul ha2 ht (abs_nonneg _) (by positivity)
  have hF : |entranceStrongBracket y| ≤ 3 * C * b ^ 2 / k := by
    rw [entranceStrongBracket_eq]
    calc
      _ ≤ |entranceStablePhase y - y 0| + |(y 0 - 1) * (entranceStablePartial y 0 - 1)| := abs_sub _ _
      _ ≤ C * b ^ 2 / k + 2 * k * (C * b ^ 2 / k ^ 2) := add_le_add hp (hmul _ _ _ hm0 hm2 hpM)
      _ = _ := by field_simp; ring
  have hFM : |-(y 0 - 1) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 0 1)| ≤
      3 * C * b ^ 2 / k ^ 2 := by
    rw [neg_mul, abs_neg]
    calc
      _ ≤ 2 * k * (C * b ^ 2 / k ^ 3) := hmul _ _ _ hm0 hm2 hMM
      _ = 2 * C * b ^ 2 / k ^ 2 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : 2 * C ≤ 3 * C) (sq_nonneg b)) (sq_nonneg k)
  have hcombine (n : ℕ) (a u w : ℝ) (ha : |a| ≤ 3 * C * b ^ 2 / k ^ n)
      (hu' : |u| ≤ C * b / k ^ n) (hw' : |w| ≤ C * b / k ^ n) :
      |a + y 3 * (u - w) - y 2 * u / 2| ≤ 6 * C * s / k ^ n := by
    have hdiff : |u - w| ≤ 2 * C * b / k ^ n := by
      calc
        _ ≤ |u| + |w| := abs_sub _ _
        _ ≤ C * b / k ^ n + C * b / k ^ n := add_le_add hu' hw'
        _ = _ := by ring
    calc
      _ ≤ |a| + |y 3 * (u - w)| + |y 2 * u / 2| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |a| + y 3 * |u - w| + y 2 * |u| / 2 := by
        rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hW, abs_of_nonneg hV]; norm_num
      _ ≤ 3 * C * b ^ 2 / k ^ n + b * (2 * C * b / k ^ n) + y 2 * (C * b / k ^ n) / 2 :=
        add_le_add (add_le_add ha (mul_le_mul hWb hdiff (abs_nonneg _) hb))
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu' hV) (by norm_num))
      _ = (5 * C * b ^ 2 + C * (y 2 * b) / 2) / k ^ n := by ring
      _ ≤ 6 * C * s / k ^ n := by
        apply (div_le_div_iff_of_pos_right (pow_pos hk0 n)).mpr
        dsimp [s]
        nlinarith only [mul_nonneg hC.le (sq_nonneg b), mul_nonneg hC.le (mul_nonneg hV hb)]
  have hT := hcombine 1 _ _ _ (by simpa using hF) (by simpa using hpU) (by simpa using hpW)
  have hsym := (contDiffAt_entranceStablePhase_two hm hu hw).isSymmSndFDerivAt (by norm_num)
  rw [hsym.eq (Pi.single 1 1) (Pi.single 0 1)] at hMU
  rw [hsym.eq (Pi.single 3 1) (Pi.single 0 1)] at hMW
  have hTM := hcombine 2 _ _ _ hFM hMU hMW
  simp only [pow_one] at hT
  have hE : |entranceStrongRemainder y| ≤ 12 * C * s := by
    have he : entranceStrongRemainder y = (entranceStablePhase y - 1) *
      (entranceStrongBracket y + y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) - y 2 * entranceStablePartial y 1 / 2) := by
      rw [entranceStrongRemainder_bracket]; ring
    rw [he]
    calc
      _ ≤ 2 * k * (6 * C * s / k) := hmul _ _ _ hchi0 hchi2 hT
      _ = _ := by field_simp; ring
  have hEM : |fderiv ℝ entranceStrongRemainder y (Pi.single 0 1)| ≤ 24 * C * s / k := by
    rw [entranceStrongRemainder_phase_derivative hm hu hw]
    calc
      _ ≤ |entranceStablePartial y 0 * (entranceStrongBracket y +
          y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) - y 2 * entranceStablePartial y 1 / 2)| +
          |(entranceStablePhase y - 1) * (-(y 0 - 1) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 0 1) +
            y 3 * (fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 1 1) -
              fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 3 1)) -
            y 2 * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 1 1) / 2)| := abs_add_le _ _
      _ ≤ 2 * (6 * C * s / k) + 2 * k * (6 * C * s / k ^ 2) := by
        apply add_le_add _ (hmul _ _ _ hchi0 hchi2 hTM)
        rw [abs_mul, abs_of_nonneg hPM0]
        exact mul_le_mul hPM2 hT (abs_nonneg _) (by norm_num)
      _ = _ := by field_simp; ring
  dsimp only
  refine ⟨hF.trans ?_, hE.trans ?_, hEM.trans ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : 3 * C ≤ 32 * C) (sq_nonneg b)) hk0.le
  · exact mul_le_mul_of_nonneg_right (by linarith : 12 * C ≤ 32 * C) hs
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : 24 * C ≤ 32 * C) hs) hk0.le

end BianchiIX
