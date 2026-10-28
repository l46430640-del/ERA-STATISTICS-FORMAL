import BianchiIX.Dynamics.EntranceOperatorBounds
import BianchiIX.Dynamics.EntranceStrongRemainder

noncomputable section

namespace BianchiIX

theorem entranceStrongRemainder_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceStrongRemainder y v =
      fderiv ℝ entranceStablePhase y v * (entranceStrongBracket y +
        y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) - y 2 * entranceStablePartial y 1 / 2) +
      (entranceStablePhase y - 1) * (fderiv ℝ entranceStrongBracket y v +
        v 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) +
        y 3 * (fderiv ℝ (fun z => entranceStablePartial z 1) y v - fderiv ℝ (fun z => entranceStablePartial z 3) y v) -
        (v 2 * entranceStablePartial y 1 + y 2 * fderiv ℝ (fun z => entranceStablePartial z 1) y v) / 2) := by
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
    Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  ring

set_option maxHeartbeats 500000 in
/-- A coarse ordinary derivative bound avoids unnecessary weighted Hessian estimates. -/
theorem exists_entranceStrongRemainder_operator_bound :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      ‖fderiv ℝ entranceStrongRemainder y‖ ≤ C * k ^ 2 := by
  obtain ⟨K, hK, HK⟩ := exists_entranceProjection_operator_bounds
  obtain ⟨R, hR, HR⟩ := exists_entranceStrongRemainder_bounds
  have hK0 : 0 < K := by linarith
  refine ⟨K * (R + 3 * K + 18), by positivity, ?_⟩
  intro k y hk hy
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu0 := hy.2.2.1.1
  have hv0 := hy.2.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hv1 := hy.2.2.2.1.2
  have hw1 : y 3 ≤ 1 := by linarith [hy.2.2.2.2.2]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hu0]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hw0]; linarith [hy.2.2.2.2.2]
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hu0 hw0
  have hb1 : y 1 + y 3 ≤ 1 := by linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hb2 : (y 1 + y 3) ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  have hF : |entranceStrongBracket y| ≤ R := (HR k y hk hy).1.trans
    ((div_le_self (by positivity) hk1).trans (by nlinarith only [mul_le_mul_of_nonneg_left hb2 hR.le]))
  obtain ⟨hP, hPP⟩ := HK k y hk hy
  have hp (i : Fin 4) : |entranceStablePartial y i| ≤ K := by
    have H := ((fderiv ℝ entranceStablePhase y).le_opNorm (Pi.single i 1)).trans
      (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
    simpa [entranceStablePartial, Pi.norm_single] using H
  have hchi := (entranceRegion_stable_radial_bounds hk hy).1
  have hchi0 : 0 ≤ entranceStablePhase y - 1 := by linarith only [hchi.1, hk0]
  have hchi2 : entranceStablePhase y - 1 ≤ 2 * k := by linarith only [hchi.2, hk0]
  have hm0 : 0 ≤ y 0 - 1 := by linarith
  have hm2 : y 0 - 1 ≤ 2 * k := by linarith [(entranceRegion_phase hk hy).2]
  have hdiff : |entranceStablePartial y 1 - entranceStablePartial y 3| ≤ 2 * K :=
    (abs_sub _ _).trans (by linarith only [hp 1, hp 3])
  have hT : |entranceStrongBracket y + y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) -
      y 2 * entranceStablePartial y 1 / 2| ≤ R + 3 * K := by
    calc
      _ ≤ |entranceStrongBracket y| + |y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3)| +
          |y 2 * entranceStablePartial y 1 / 2| := (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ R + 1 * (2 * K) + (1 * K) / 2 := by
        rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hv0]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact add_le_add (add_le_add hF (mul_le_mul hw1 hdiff (abs_nonneg _) (by norm_num)))
          (div_le_div_of_nonneg_right (mul_le_mul hv1 (hp 1) (abs_nonneg _) (by norm_num)) (by norm_num))
      _ ≤ _ := by linarith only [hK0]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv (i : Fin 4) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hPv : |fderiv ℝ entranceStablePhase y v| ≤ K * ‖v‖ :=
    ((fderiv ℝ entranceStablePhase y).le_opNorm v).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg v))
  have hQv (i : Fin 4) : |fderiv ℝ (fderiv ℝ entranceStablePhase) y v (Pi.single i 1)| ≤ K * ‖v‖ := by
    have H := (((fderiv ℝ (fderiv ℝ entranceStablePhase) y) v).le_opNorm (Pi.single i 1)).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ entranceStablePhase) y).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hPP (norm_nonneg v))) (norm_nonneg _))
    simpa [Pi.norm_single] using H
  have hpv (i : Fin 4) : |fderiv ℝ (fun z => entranceStablePartial z i) y v| ≤ K * ‖v‖ := by
    rw [entranceStablePartial_fderiv hm hu hw]
    exact hQv i
  have hFv : |fderiv ℝ entranceStrongBracket y v| ≤ 4 * K * k * ‖v‖ := by
    rw [entranceStrongBracket_fderiv hm hu hw]
    calc
      _ ≤ |fderiv ℝ entranceStablePhase y v| + |v 0 * entranceStablePartial y 0| +
          |(y 0 - 1) * fderiv ℝ (fderiv ℝ entranceStablePhase) y v (Pi.single 0 1)| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ K * ‖v‖ + ‖v‖ * K + 2 * k * (K * ‖v‖) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hm0]
        exact add_le_add (add_le_add hPv (mul_le_mul (hv 0) (hp 0) (abs_nonneg _) (norm_nonneg v)))
          (mul_le_mul hm2 (hQv 0) (abs_nonneg _) (by positivity))
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hk1 (mul_nonneg hK0.le (norm_nonneg v))]
  have hDv : |fderiv ℝ (fun z => entranceStablePartial z 1) y v - fderiv ℝ (fun z => entranceStablePartial z 3) y v| ≤ 2 * K * ‖v‖ :=
    (abs_sub _ _).trans (by linarith only [hpv 1, hpv 3])
  have hTv : |fderiv ℝ entranceStrongBracket y v + v 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) +
      y 3 * (fderiv ℝ (fun z => entranceStablePartial z 1) y v - fderiv ℝ (fun z => entranceStablePartial z 3) y v) -
      (v 2 * entranceStablePartial y 1 + y 2 * fderiv ℝ (fun z => entranceStablePartial z 1) y v) / 2| ≤ 9 * K * k * ‖v‖ := by
    calc
      _ ≤ |fderiv ℝ entranceStrongBracket y v| + |v 3 * (entranceStablePartial y 1 - entranceStablePartial y 3)| +
          |y 3 * (fderiv ℝ (fun z => entranceStablePartial z 1) y v - fderiv ℝ (fun z => entranceStablePartial z 3) y v)| +
          (|v 2 * entranceStablePartial y 1| + |y 2 * fderiv ℝ (fun z => entranceStablePartial z 1) y v|) / 2 := by
        have ht (a b c d e : ℝ) : |a + b + c - (d + e) / 2| ≤ |a| + |b| + |c| + (|d| + |e|) / 2 := by
          calc
            _ ≤ |a + b + c| + |(d + e) / 2| := abs_sub _ _
            _ ≤ |a| + |b| + |c| + (|d| + |e|) / 2 := by
              rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
              exact add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl))
                (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num))
        exact ht _ _ _ _ _
      _ ≤ 4 * K * k * ‖v‖ + ‖v‖ * (2 * K) + 1 * (2 * K * ‖v‖) + (‖v‖ * K + 1 * (K * ‖v‖)) / 2 := by
        simp only [abs_mul, abs_of_nonneg hw0, abs_of_nonneg hv0]
        exact add_le_add (add_le_add (add_le_add hFv (mul_le_mul (hv 3) hdiff (abs_nonneg _) (norm_nonneg v)))
          (mul_le_mul hw1 hDv (abs_nonneg _) (by norm_num)))
          (div_le_div_of_nonneg_right (add_le_add (mul_le_mul (hv 2) (hp 1) (abs_nonneg _) (norm_nonneg v))
            (mul_le_mul hv1 (hpv 1) (abs_nonneg _) (by norm_num))) (by norm_num))
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hk1 (mul_nonneg hK0.le (norm_nonneg v))]
  rw [Real.norm_eq_abs, entranceStrongRemainder_fderiv hm hu hw]
  calc
    _ ≤ |fderiv ℝ entranceStablePhase y v| * |entranceStrongBracket y +
        y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) - y 2 * entranceStablePartial y 1 / 2| +
        (entranceStablePhase y - 1) * |fderiv ℝ entranceStrongBracket y v +
          v 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) +
          y 3 * (fderiv ℝ (fun z => entranceStablePartial z 1) y v - fderiv ℝ (fun z => entranceStablePartial z 3) y v) -
          (v 2 * entranceStablePartial y 1 + y 2 * fderiv ℝ (fun z => entranceStablePartial z 1) y v) / 2| := by
      simpa only [abs_mul, abs_of_nonneg hchi0] using abs_add_le
        (fderiv ℝ entranceStablePhase y v * (entranceStrongBracket y +
          y 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) - y 2 * entranceStablePartial y 1 / 2))
        ((entranceStablePhase y - 1) * (fderiv ℝ entranceStrongBracket y v +
          v 3 * (entranceStablePartial y 1 - entranceStablePartial y 3) +
          y 3 * (fderiv ℝ (fun z => entranceStablePartial z 1) y v - fderiv ℝ (fun z => entranceStablePartial z 3) y v) -
          (v 2 * entranceStablePartial y 1 + y 2 * fderiv ℝ (fun z => entranceStablePartial z 1) y v) / 2))
    _ ≤ (K * ‖v‖) * (R + 3 * K) + 2 * k * (9 * K * k * ‖v‖) :=
      add_le_add (mul_le_mul hPv hT (abs_nonneg _) (by positivity)) (mul_le_mul hchi2 hTv (abs_nonneg _) (by positivity))
    _ = K * (R + 3 * K) * ‖v‖ + 18 * K * k ^ 2 * ‖v‖ := by ring
    _ ≤ (K * (R + 3 * K) * ‖v‖) * k ^ 2 + 18 * K * k ^ 2 * ‖v‖ :=
      add_le_add (le_mul_of_one_le_right (by positivity) hk2) le_rfl
    _ = _ := by ring

end BianchiIX
