import BianchiIX.Dynamics.EntranceDriftEstimates

noncomputable section

namespace BianchiIX

/-- The basic drift bound already controls both source weights used in the return transport identity. -/
theorem exists_entrance_transport_drift_bound :
    ∃ A > (0 : ℝ), ∀ (k θ : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      (θ = 1 ∨ θ = 1 / k ^ 2) →
      |entranceRadialDrift y| ≤ A * (y 1 * y 2 + θ * (y 2 * y 3) ^ 2) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceRadialDrift_basic_bounds
  refine ⟨A, hA, ?_⟩
  intro k θ y hk hy hv hθ
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk hy hv
  have H := (HA k y hk hy hv Ψ HΨ).1
  rcases hθ with rfl | rfl
  · apply H.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hA.le)
    have hk1 : 1 ≤ k := by linarith
    calc
      _ ≤ y 2 ^ 2 * y 3 ^ 2 := div_le_self (by positivity) (one_le_pow₀ hk1)
      _ = _ := by ring
  · convert! H using 1
    ring

end BianchiIX
