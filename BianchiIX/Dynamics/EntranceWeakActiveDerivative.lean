import BianchiIX.Analysis.EntranceActivePhaseEstimates
import BianchiIX.Dynamics.EntranceWeakRadialBounds

noncomputable section

namespace BianchiIX

theorem entranceWeakNumerator_active_derivative {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    fderiv ℝ entranceWeakNumerator y (Pi.single 2 1) = 0 := by
  have hz : stableRestriction (Pi.single (2 : Fin 4) (1 : ℝ)) = 0 := by
    ext i
    fin_cases i <;> simp [stableRestriction]
  rw [entranceWeakNumerator_fderiv hm hu hw, entranceStablePhase_fderiv hm hu hw,
    entranceStablePhase_hessian hm hu hw, hz]
  simp

/-- At fixed corrected radius, the weak numerator varies only through M. -/
theorem EntranceRadialInverseAt.weak_active_partial {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    let z := entranceRadialCoordinates y
    let m := fderiv ℝ Ψ z (Pi.single 2 1) 0
    fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 2 1) =
      fderiv ℝ entranceWeakNumerator y (Pi.single 0 1) * m /
        (entranceStableRadius y * entranceClockRate y) -
      entranceRadialWeakCoefficient y * ((m - y 1) / entranceClockRate y) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hn := (H.scalar_partials ((contDiffAt_entranceWeakNumerator_one hm hu hw).differentiableAt (by norm_num))).2.2.1
  dsimp only
  rw [H.weak_differential hk hy hv, hn, entranceWeakNumerator_active_derivative hm hu hw,
    H.phase_partials.2.2.1, H.clock_partials.2.2.1]
  simp only [Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2), zero_div, zero_add, zero_sub]
  ring

theorem exists_entranceRadialWeak_active_bound :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) (entranceRadialCoordinates y) (Pi.single 2 1)| ≤
          C * (y 1 + y 3) ^ 2 * (y 2 / k ^ 4 + y 1 / k ^ 3) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceWeakNumerator_bounds
  obtain ⟨B, hB, HB⟩ := exists_entranceRadialWeakCoefficient_bounds
  obtain ⟨J, _, HJ⟩ := exists_entranceRadialInverse_column_bounds
  refine ⟨16 * A + 10 * B, by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  have hk0 : 0 < k := by linarith
  have hr := (entranceRegion_stable_radial_bounds hk hy).2.1.1
  have hD : k / 2 ≤ entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]
  have hrD : k ^ 2 / 4 ≤ entranceStableRadius y * entranceClockRate y := by
    have Hp := mul_le_mul hr hD (by positivity : 0 ≤ k / 2) (entranceStableRadius_pos hv).le
    nlinarith only [Hp]
  rw [H.weak_active_partial hk hy hv]
  exact entrance_weak_active_quotient_bound (by linarith) hrD hD hy.2.2.1.1 hv.le hA.le hB.le
    (HJ k y hk hy hv Ψ H).2.2.1 (HA k y hk hy).2.1 (HB k y hk hy hv Ψ H).1

end BianchiIX
