import BianchiIX.Dynamics.EntranceStrongRadialBounds
import BianchiIX.Dynamics.EntranceWeakRadialBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def entranceRadialDrift (y : ProjectiveState) : ℝ :=
  y 1 * y 2 * entranceRadialStrongCoefficient y + y 2 ^ 2 * entranceRadialWeakCoefficient y

theorem entranceRadialDrift_eq_log_rate {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    entranceRadialDrift y = fderiv ℝ entranceStableRadius y (projectiveField y) / entranceClockRate y :=
  (entranceStableRadius_log_rate hm hu hw hv).symm

theorem EntranceRadialInverseAt.drift_radial_derivative {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    let z := entranceRadialCoordinates y
    fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z (Pi.single 0 1) =
      y 1 * y 2 * fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 0 1) +
      y 2 ^ 2 * fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 0 1) := by
  have heq : (fun z => entranceRadialDrift (Ψ z)) =ᶠ[𝓝 (entranceRadialCoordinates y)]
      (fun z => z 1 * z 2 * entranceRadialStrongCoefficient (Ψ z) + z 2 ^ 2 * entranceRadialWeakCoefficient (Ψ z)) := by
    filter_upwards [H.wall_coordinates] with z hz
    simp only [entranceRadialDrift, hz.1, hz.2.1]
  obtain ⟨hA, hB⟩ := H.coefficients_regular hk hy hv
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i (entranceRadialCoordinates y)
  have hsum := (((hd 1).mul (hd 2)).mul (hA.differentiableAt (by norm_num)).hasFDerivAt).add
    (((hd 2).pow 2).mul (hB.differentiableAt (by norm_num)).hasFDerivAt)
  change HasFDerivAt (fun z => z 1 * z 2 * entranceRadialStrongCoefficient (Ψ z) + z 2 ^ 2 * entranceRadialWeakCoefficient (Ψ z)) _
    (entranceRadialCoordinates y) at hsum
  dsimp only
  rw [heq.fderiv_eq, hsum.fderiv]
  simp [add_apply, smul_apply, ContinuousLinearMap.proj_apply, entranceRadialCoordinates, Pi.mul_apply]

/-- Both factors in the exact radial drift retain their parameter decay in (C.21). -/
theorem exists_entranceRadialDrift_radial_bound :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        |fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1)| ≤
          C * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * (y 1 + y 3) ^ 2 / k ^ 3) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceRadialStrong_radial_bounds
  obtain ⟨B, hB, HB⟩ := exists_entranceRadialWeakCoefficient_bounds
  refine ⟨A + B, by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  have hstrong := (HA k y hk hy hv Ψ H).2.1
  have hweak := (HB k y hk hy hv Ψ H).2.1
  have huv : 0 ≤ y 1 * y 2 := mul_nonneg hy.2.2.1.1 hy.2.2.2.1.1
  have hk0 : 0 < k := by linarith
  have habs (c a : ℝ) (hc : 0 ≤ c) : |c * a| = c * |a| := by rw [abs_mul, abs_of_nonneg hc]
  rw [H.drift_radial_derivative hk hy hv]
  calc
    _ ≤ y 1 * y 2 * |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1)| +
        y 2 ^ 2 * |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1)| :=
      (abs_add_le _ _).trans (add_le_add (le_of_eq (habs _ _ huv)) (le_of_eq (habs _ _ (sq_nonneg (y 2)))))
    _ ≤ y 1 * y 2 * (A / k ^ 2) + y 2 ^ 2 * (B * (y 1 + y 3) ^ 2 / k ^ 3) :=
      add_le_add (mul_le_mul_of_nonneg_left hstrong huv) (mul_le_mul_of_nonneg_left hweak (sq_nonneg _))
    _ = A * (y 1 * y 2 / k ^ 2) + B * (y 2 ^ 2 * (y 1 + y 3) ^ 2 / k ^ 3) := by ring
    _ ≤ _ := by
      have hx : 0 ≤ y 1 * y 2 / k ^ 2 := div_nonneg huv (sq_nonneg k)
      have hz : 0 ≤ y 2 ^ 2 * (y 1 + y 3) ^ 2 / k ^ 3 := by positivity
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le) hx)
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) hz)

end BianchiIX
