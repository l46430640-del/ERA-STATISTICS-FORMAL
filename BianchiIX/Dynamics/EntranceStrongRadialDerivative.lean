import BianchiIX.Dynamics.EntranceStrongRemainder
import BianchiIX.Dynamics.EntranceRadialQuotient

noncomputable section

namespace BianchiIX

theorem entranceRadialStrongCoefficient_split (y : ProjectiveState) :
    entranceRadialStrongCoefficient y = -entranceStableRadius y / entranceClockRate y +
      entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) := by
  by_cases hr : entranceStableRadius y = 0
  · simp [entranceRadialStrongCoefficient, hr]
  by_cases hd : entranceClockRate y = 0
  · simp [entranceRadialStrongCoefficient, hd]
  exact entranceRadialStrongCoefficient_decomposition hr hd

theorem EntranceRadialInverseAt.strong_differential {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (v : ProjectiveState) :
    let z := entranceRadialCoordinates y
    let Q := fderiv ℝ (fun z => entranceClockRate (Ψ z)) z
    fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z v =
      (entranceStableRadius y * Q v - entranceClockRate y * v 0) / entranceClockRate y ^ 2 +
      fderiv ℝ (fun z => entranceStrongRemainder (Ψ z)) z v / (entranceStableRadius y * entranceClockRate y) -
      entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) *
        (v 0 / entranceStableRadius y + Q v / entranceClockRate y) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hr := (contDiffAt_entranceStableRadius_two hm hu hw hv).differentiableAt (by norm_num)
  have hE := (contDiffAt_entranceStrongRemainder_one hm hu hw).differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ entranceClockRate y := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  have hr0 := (entranceStableRadius_pos hv).ne'
  have hD0 := (entranceRegion_clock_pos hk hy).ne'
  have hleft : DifferentiableAt ℝ (fun z => entranceStableRadius (Ψ z) / entranceClockRate (Ψ z))
      (entranceRadialCoordinates y) := by
    have hf : DifferentiableAt ℝ (fun x => entranceStableRadius x / entranceClockRate x) (Ψ (entranceRadialCoordinates y)) := by
      rw [H.apply_base]
      exact hr.mul ((hasFDerivAt_inv hD0).differentiableAt.comp y hD)
    exact hf.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have hright : DifferentiableAt ℝ
      (fun z => entranceStrongRemainder (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z)))
      (entranceRadialCoordinates y) := by
    have hf : DifferentiableAt ℝ
        (fun x => entranceStrongRemainder x / (entranceStableRadius x * entranceClockRate x)) (Ψ (entranceRadialCoordinates y)) := by
      rw [H.apply_base]
      exact hE.mul ((hasFDerivAt_inv (mul_ne_zero hr0 hD0)).differentiableAt.comp y (hr.mul hD))
    exact hf.comp _ (H.contDiffAt.differentiableAt (by norm_num))
  have heq : (fun z => entranceRadialStrongCoefficient (Ψ z)) =
      (fun z => -(entranceStableRadius (Ψ z) / entranceClockRate (Ψ z)) +
        entranceStrongRemainder (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z))) := by
    funext z
    simpa only [neg_div] using entranceRadialStrongCoefficient_split (Ψ z)
  have hsum := hleft.hasFDerivAt.neg.add hright.hasFDerivAt
  change HasFDerivAt (fun z => -(entranceStableRadius (Ψ z) / entranceClockRate (Ψ z)) +
    entranceStrongRemainder (Ψ z) / (entranceStableRadius (Ψ z) * entranceClockRate (Ψ z))) _ (entranceRadialCoordinates y) at hsum
  dsimp only
  rw [heq, hsum.fderiv]
  simp only [add_apply, neg_apply]
  rw [H.clock_quotient_differential hr hD0 v, H.radius_differential v,
    H.radial_quotient_differential hE hr0 hD0 v]
  field_simp
  ring

theorem EntranceRadialInverseAt.clock_radial_remainder {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hchi : entranceStablePhase y - 1 ≠ 0) (hPM : entranceStablePartial y 0 ≠ 0) :
    entranceStableRadius y *
        fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1) - entranceClockRate y =
      entranceStrongBracket y / entranceStablePartial y 0 +
        y 2 ^ 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) + coupling (y 1) (y 2) (y 3) := by
  rw [H.clock_radial_cancellation, entranceStableRadius_sq]
  unfold entranceStrongBracket
  field_simp
  ring

theorem exists_entranceClock_radial_cancellation_bound :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        |entranceStableRadius y *
            fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1) - entranceClockRate y| ≤
          C * (y 2 ^ 2 / k + y 1 * y 2 + (y 1 + y 3) ^ 2) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceStrongRemainder_bounds
  refine ⟨2 * C + 5, by positivity, ?_⟩
  intro k y hk hy Ψ H
  let b := y 1 + y 3
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hU := hy.2.2.1.1
  have hV := hy.2.2.2.1.1
  have hW := hy.2.2.2.2.1
  have hb : 0 ≤ b := add_nonneg hU hW
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  have hchi0 : 0 < entranceStablePhase y - 1 := by linarith [hchi.1]
  have hPM0 : 0 < entranceStablePartial y 0 := by linarith [hPM.1]
  have hden : k / 4 ≤ (entranceStablePhase y - 1) * entranceStablePartial y 0 := by
    have Hprod := mul_le_mul hchi.1 hPM.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hchi0.le
    nlinarith only [Hprod]
  have hF : |entranceStrongBracket y / entranceStablePartial y 0| ≤ 2 * C * b ^ 2 := by
    rw [abs_div, abs_of_pos hPM0]
    calc
      _ ≤ (C * b ^ 2 / k) / (1 / 2) := div_le_div₀ (by positivity) (HC k y hk hy).1 (by norm_num) hPM.1
      _ = 2 * C * b ^ 2 / k := by ring
      _ ≤ _ := div_le_self (by positivity) hk1
  have hterm : |y 2 ^ 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0)| ≤ 4 * (y 2 ^ 2 / k) := by
    rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (mul_pos hchi0 hPM0)]
    calc
      _ ≤ y 2 ^ 2 / (k / 4) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
      _ = _ := by ring
  have hc : |coupling (y 1) (y 2) (y 3)| ≤ y 1 * y 2 + b ^ 2 := by
    have hdiff : |y 3 - y 1| ≤ b := by
      calc
        _ ≤ |y 3| + |y 1| := abs_sub _ _
        _ = b := by rw [abs_of_nonneg hW, abs_of_nonneg hU]; dsimp [b]; ring
    have heq : coupling (y 1) (y 2) (y 3) = y 1 * y 2 + y 1 * (y 3 - y 1) := by unfold coupling; ring
    rw [heq]
    calc
      _ ≤ |y 1 * y 2| + |y 1 * (y 3 - y 1)| := abs_add_le _ _
      _ = y 1 * y 2 + y 1 * |y 3 - y 1| := by rw [abs_of_nonneg (mul_nonneg hU hV), abs_mul, abs_of_nonneg hU]
      _ ≤ y 1 * y 2 + b * b := add_le_add le_rfl
        (mul_le_mul (by dsimp [b]; linarith only [hW]) hdiff (abs_nonneg _) hb)
      _ = _ := by ring
  rw [H.clock_radial_remainder hchi0.ne' hPM0.ne']
  calc
    _ ≤ |entranceStrongBracket y / entranceStablePartial y 0| +
        |y 2 ^ 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0)| + |coupling (y 1) (y 2) (y 3)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2 * C * b ^ 2 + 4 * (y 2 ^ 2 / k) + (y 1 * y 2 + b ^ 2) := add_le_add (add_le_add hF hterm) hc
    _ ≤ _ := by
      have hx : 0 ≤ y 2 ^ 2 / k := by positivity
      have hz : 0 ≤ y 1 * y 2 := mul_nonneg hU hV
      change _ ≤ (2 * C + 5) * (y 2 ^ 2 / k + y 1 * y 2 + b ^ 2)
      nlinarith only [hC, hx, hz, sq_nonneg b, mul_nonneg hC.le hx, mul_nonneg hC.le hz]

end BianchiIX
