import BianchiIX.Dynamics.EntranceStrongOrdinaryDerivative
import BianchiIX.Dynamics.EntranceStrongRadialBounds
import BianchiIX.Dynamics.EntranceWeakRadialBounds

noncomputable section

namespace BianchiIX

set_option maxHeartbeats 600000 in
/-- The complete strong coefficient derivative in the actual radial chart is uniformly bounded. -/
theorem exists_entranceRadialStrong_derivative_bound :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        |entranceRadialStrongCoefficient y| +
          ‖fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) (entranceRadialCoordinates y)‖ ≤ C := by
  obtain ⟨S, hS, HS⟩ := exists_entranceStrongRemainder_operator_bound
  obtain ⟨R, hR, HR⟩ := exists_entranceStrongRemainder_bounds
  obtain ⟨J, hJ, HJ⟩ := exists_entranceRadialInverse_operator_bound
  obtain ⟨T, hT, HT⟩ := exists_entranceRadialStrong_radial_bounds
  have hJ0 : 0 < J := by linarith
  let K := 56 * J + 8 + 4 * S * J + 8 * R * (2 + 14 * J)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨T + K, by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu0 := hy.2.2.1.1
  have hv0 := hy.2.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hu0]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hw0]; linarith [hy.2.2.2.2.2]
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hu0 hw0
  have hb1 : y 1 + y 3 ≤ 1 := by linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hb2 : (y 1 + y 3) ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  have hs2 : y 2 * (y 1 + y 3) + (y 1 + y 3) ^ 2 ≤ 2 := by
    have Hprod := mul_le_mul hy.2.2.2.1.2 hb1 hb (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [Hprod, hb2]
  have hEval : |entranceStrongRemainder y| ≤ 2 * R :=
    (HR k y hk hy).2.1.trans (by nlinarith only [mul_le_mul_of_nonneg_left hs2 hR.le])
  have hEnorm := HS k y hk hy
  have hJnorm := HJ k y hk hy hv Ψ H
  have hL (v : ProjectiveState) : ‖entranceRadialInverseDifferential y v‖ ≤ J * ‖v‖ := by
    rw [← H.hasFDerivAt.fderiv]
    exact ((fderiv ℝ Ψ (entranceRadialCoordinates y)).le_opNorm v).trans (mul_le_mul_of_nonneg_right hJnorm (norm_nonneg v))
  have hEreg := (contDiffAt_entranceStrongRemainder_one hm hu hw).differentiableAt (by norm_num)
  have hDreg : DifferentiableAt ℝ entranceClockRate y := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  obtain ⟨_, hr, _⟩ := entranceRegion_stable_radial_bounds hk hy
  have hD := entranceRegion_speed hk hy
  have hr0 := entranceStableRadius_pos hv
  have hD0 := entranceRegion_clock_pos hk hy
  have hDlo : k / 2 ≤ entranceClockRate y := by linarith only [hD.1, hk0]
  have hDhi : entranceClockRate y ≤ 2 * k := by linarith only [hD.2, hk0]
  have hden : k ^ 2 / 4 ≤ entranceStableRadius y * entranceClockRate y := by
    have Hprod := mul_le_mul hr.1 hDlo (by positivity) hr0.le
    nlinarith only [Hprod]
  have hDsq : k ^ 2 / 4 ≤ entranceClockRate y ^ 2 := by
    have Hp := pow_le_pow_left₀ (show 0 ≤ k / 2 by positivity) hDlo 2
    nlinarith only [Hp]
  have hEquot : |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y)| ≤ 8 * R := by
    rw [abs_div, abs_of_pos (mul_pos hr0 hD0)]
    calc
      _ ≤ (2 * R) / (k ^ 2 / 4) := div_le_div₀ (by positivity) hEval (by positivity) hden
      _ = 8 * R / k ^ 2 := by ring
      _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ hk1)
  have hnorm : ‖fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) (entranceRadialCoordinates y)‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK.le
    intro v
    let Q := fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) v
    let E := fderiv ℝ (fun z => entranceStrongRemainder (Ψ z)) (entranceRadialCoordinates y) v
    have hvnorm : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
    have hQ : |Q| ≤ 7 * J * ‖v‖ := by
      dsimp only [Q]
      rw [H.scalar_differential hDreg]
      exact (entranceClockRate_fderiv_bound hy _).trans
        ((mul_le_mul_of_nonneg_left (hL v) (by norm_num)).trans_eq (by ring))
    have hE : |E| ≤ S * k ^ 2 * (J * ‖v‖) := by
      dsimp only [E]
      rw [H.scalar_differential hEreg]
      exact ((fderiv ℝ entranceStrongRemainder y).le_opNorm _).trans
        (mul_le_mul hEnorm (hL v) (norm_nonneg _) (by positivity))
    have hlead : |(entranceStableRadius y * Q - entranceClockRate y * v 0) / entranceClockRate y ^ 2| ≤
        (56 * J + 8) * ‖v‖ := by
      have hnum : |entranceStableRadius y * Q - entranceClockRate y * v 0| ≤ (14 * J + 2) * k * ‖v‖ := by
        calc
          _ ≤ |entranceStableRadius y * Q| + |entranceClockRate y * v 0| := abs_sub _ _
          _ ≤ (2 * k) * (7 * J * ‖v‖) + (2 * k) * ‖v‖ := by
            rw [abs_mul, abs_mul, abs_of_pos hr0, abs_of_pos hD0]
            exact add_le_add (mul_le_mul hr.2 hQ (abs_nonneg _) (by positivity))
              (mul_le_mul hDhi hvnorm (abs_nonneg _) (by positivity))
          _ = _ := by ring
      rw [abs_div, abs_of_nonneg (sq_nonneg (entranceClockRate y))]
      calc
        _ ≤ ((14 * J + 2) * k * ‖v‖) / (k ^ 2 / 4) := div_le_div₀ (by positivity) hnum (by positivity) hDsq
        _ = ((56 * J + 8) * ‖v‖) / k := by field_simp; ring
        _ ≤ _ := div_le_self (by positivity) hk1
    have hEfrac : |E / (entranceStableRadius y * entranceClockRate y)| ≤ 4 * S * J * ‖v‖ := by
      rw [abs_div, abs_of_pos (mul_pos hr0 hD0)]
      calc
        _ ≤ (S * k ^ 2 * (J * ‖v‖)) / (k ^ 2 / 4) := div_le_div₀ (by positivity) hE (by positivity) hden
        _ = _ := by field_simp
    have hlog : |v 0 / entranceStableRadius y + Q / entranceClockRate y| ≤ (2 + 14 * J) * ‖v‖ := by
      calc
        _ ≤ |v 0 / entranceStableRadius y| + |Q / entranceClockRate y| := abs_add_le _ _
        _ ≤ ‖v‖ / (k / 2) + (7 * J * ‖v‖) / (k / 2) := by
          rw [abs_div, abs_div, abs_of_pos hr0, abs_of_pos hD0]
          exact add_le_add (div_le_div₀ (norm_nonneg v) hvnorm (by positivity) hr.1)
            (div_le_div₀ (by positivity) hQ (by positivity) hDlo)
        _ = ((2 + 14 * J) * ‖v‖) / k := by ring
        _ ≤ _ := div_le_self (by positivity) hk1
    rw [Real.norm_eq_abs, H.strong_differential hk hy hv]
    change |(entranceStableRadius y * Q - entranceClockRate y * v 0) / entranceClockRate y ^ 2 +
      E / (entranceStableRadius y * entranceClockRate y) -
      entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) *
        (v 0 / entranceStableRadius y + Q / entranceClockRate y)| ≤ _
    calc
      _ ≤ |(entranceStableRadius y * Q - entranceClockRate y * v 0) / entranceClockRate y ^ 2| +
          |E / (entranceStableRadius y * entranceClockRate y)| +
          |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) *
            (v 0 / entranceStableRadius y + Q / entranceClockRate y)| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (56 * J + 8) * ‖v‖ + 4 * S * J * ‖v‖ + 8 * R * ((2 + 14 * J) * ‖v‖) := by
        apply add_le_add (add_le_add hlead hEfrac)
        rw [abs_mul]
        exact mul_le_mul hEquot hlog (abs_nonneg _) (by positivity)
      _ = _ := by dsimp [K]; ring
  exact add_le_add (HT k y hk hy hv Ψ H).1 hnorm

/-- A single constant gives all estimates of equation (C.20) in the actual radial chart. -/
theorem exists_entranceRadialCoefficient_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let b := y 1 + y 3
        let z := entranceRadialCoordinates y
        let LA := fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z
        let LB := fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z
        |entranceRadialStrongCoefficient y| + ‖LA‖ ≤ C ∧
        |entranceRadialWeakCoefficient y| ≤ C * b ^ 2 / k ^ 2 ∧
        |LB (Pi.single 0 1)| ≤ C * b ^ 2 / k ^ 3 ∧
        |LB (Pi.single 1 1)| + |LB (Pi.single 3 1)| ≤ C * b / k ^ 2 := by
  obtain ⟨A, hA, HA⟩ := exists_entranceRadialStrong_derivative_bound
  obtain ⟨B, hB, HB⟩ := exists_entranceRadialWeakCoefficient_bounds
  refine ⟨A + B, by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  obtain ⟨h0, h1, h2⟩ := HB k y hk hy hv Ψ H
  have hAB : B ≤ A + B := le_add_of_nonneg_left hA.le
  have hk0 : 0 < k := by linarith
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  exact ⟨(HA k y hk hy hv Ψ H).trans (le_add_of_nonneg_right hB.le),
    h0.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAB (sq_nonneg _)) (sq_nonneg k)),
    h1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAB (sq_nonneg _)) (by positivity)),
    h2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAB hb) (sq_nonneg k))⟩

end BianchiIX
