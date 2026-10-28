import BianchiIX.Dynamics.EntranceWallLogRates

noncomputable section

namespace BianchiIX

theorem EntranceRadialInverseAt.wallLogRates_regular {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    ContDiffAt ℝ 2 (fun z => entranceStrongLogRate (Ψ z)) (entranceRadialCoordinates y) ∧
      ContDiffAt ℝ 2 (fun z => entranceWeakLogRate (Ψ z)) (entranceRadialCoordinates y) := by
  obtain ⟨hs, hw⟩ := contDiffAt_entranceWallLogRates 2 (entranceRegion_clock_pos hk hy).ne'
  have hs' : ContDiffAt ℝ 2 entranceStrongLogRate (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]; exact hs
  have hw' : ContDiffAt ℝ 2 entranceWeakLogRate (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]; exact hw
  exact ⟨hs'.comp _ H.contDiffAt, hw'.comp _ H.contDiffAt⟩

/-- The weak rate's radial and wall derivatives retain the exact clock cancellation. -/
theorem EntranceRadialInverseAt.weakLogRate_partials {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    let z := entranceRadialCoordinates y
    let L := fderiv ℝ (fun z => entranceWeakLogRate (Ψ z)) z
    let M := fderiv ℝ Ψ z
    L (Pi.single 0 1) = 2 * (1 + coupling (y 1) (y 2) (y 3)) * M (Pi.single 0 1) 0 / entranceClockRate y ^ 2 ∧
      L (Pi.single 1 1) = (2 * (1 + coupling (y 1) (y 2) (y 3)) * M (Pi.single 1 1) 0 -
        2 * y 0 * (y 2 + y 3 - 2 * y 1)) / entranceClockRate y ^ 2 ∧
      L (Pi.single 3 1) = (2 * (1 + coupling (y 1) (y 2) (y 3)) * M (Pi.single 3 1) 0 -
        2 * y 0 * y 1) / entranceClockRate y ^ 2 := by
  have hD := (entranceRegion_clock_pos hk hy).ne'
  have hf := ((contDiffAt_entranceWallLogRates 1 hD).2.differentiableAt (by norm_num))
  obtain ⟨n0, n1, _, n3⟩ := H.scalar_partials hf
  obtain ⟨m0, m1, _, m3⟩ := H.phase_partials
  have hd (v : ProjectiveState) := (entranceWallLogRates_fderiv hD v).2
  dsimp only
  rw [n0, n1, n3, m0, m1, m3]
  refine ⟨?_, ?_, ?_⟩
  all_goals simp [hd]
  all_goals ring

end BianchiIX
