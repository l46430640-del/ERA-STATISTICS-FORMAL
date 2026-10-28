import BianchiIX.Dynamics.EntranceWeakActiveDerivative
import BianchiIX.Dynamics.EntranceRadialVariationBounds

noncomputable section

namespace BianchiIX

def entrancePhaseActiveSource (y : ProjectiveState) : ℝ :=
  y 2 * entranceRadialDriftDifferential y (Pi.single 2 1)

theorem continuousAt_entrancePhaseActiveSource {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContinuousAt entrancePhaseActiveSource y :=
  (continuousAt_apply 2 y).mul (continuousAt_entranceRadialDriftDifferential_apply hk hy hv (Pi.single 2 1))

/-- The activity forcing keeps the pure weak-wall term at order k to the minus four. -/
theorem exists_entrancePhaseActiveSource_bound :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      k * (y 1 + y 3) ^ 2 ≤ 1 →
      |entrancePhaseActiveSource y| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 / k ^ 4) := by
  obtain ⟨S, hS, HS⟩ := exists_entranceRadialStrong_derivative_bound
  obtain ⟨T, hT, HT⟩ := exists_entranceRadialWeakCoefficient_refined_bounds
  obtain ⟨R, hR, HR⟩ := exists_entranceRadialWeak_active_bound
  refine ⟨S + 2 * T + 3 * R, by positivity, ?_⟩
  intro k y hk hy hv hsmall
  obtain ⟨Ψ, H⟩ := exists_entranceRegion_radial_inverse hk hy hv
  let LA := fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) (entranceRadialCoordinates y)
  have hLA : |LA (Pi.single 2 1)| ≤ ‖LA‖ := by
    simpa only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using LA.le_opNorm (Pi.single 2 1)
  have hA := (add_le_add le_rfl hLA).trans (HS k y hk hy hv Ψ H)
  have hd := (H.drift_differential hk hy hv).2 (Pi.single 2 1)
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2), zero_mul, zero_add, mul_one] at hd
  unfold entrancePhaseActiveSource
  rw [← H.radialDriftDifferential_eq hk hy hv, hd]
  exact entrance_active_drift_bound (by linarith) hy.2.2.1.1 hv.le hy.2.2.2.1.2 hy.2.2.2.2.1
    (by linarith [hy.2.2.1.2, hy.2.2.2.2.2]) hS.le hT.le hR.le hA
    (HT k y hk hy hsmall hv Ψ H).1 (HR k y hk hy hv Ψ H)

end BianchiIX
