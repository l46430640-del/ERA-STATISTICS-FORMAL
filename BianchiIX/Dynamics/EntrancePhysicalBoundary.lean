import BianchiIX.Dynamics.EntrancePhysicalResponse
import BianchiIX.Analysis.TwoWallCapLimit

noncomputable section

namespace BianchiIX

/-- All of (C.39) extends to both zero stable walls, including the closed refined domain. -/
theorem exists_entrance_physical_bounds_nonneg :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 ≤ y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let L := -Real.log (y 2)
      let ω := Real.exp (-2 * L / k)
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      ContDiffAt ℝ 2 F z ∧
      |F z - z 0| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + ω)) / k ∧
      |fderiv ℝ F z (Pi.single 0 1) - 1| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + (1 + L / k) * ω)) / k ^ 2 ∧
      |fderiv ℝ F z (Pi.single 1 1)| ≤ C * y 2 / k ∧
      |fderiv ℝ F z (Pi.single 2 1)| ≤ C * (y 1 + y 2 * (y 3) ^ 2) ∧
      |fderiv ℝ F z (Pi.single 3 1)| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * y 3 * (θ + ω)) / k := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_physical_bounds
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y θ k hk hm hu hv hw hθ
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hεsmall⟩
  have hy : entranceRegion k y := ⟨hm, by simp [k]; positivity, hu', ⟨hv.1.le, hv.2.le⟩, hw'⟩
  have hM : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hU : |y 1| < 1 / 200 := by rw [abs_of_nonneg hu.1]; linarith [hu'.2]
  have hW : |y 3| < 1 / 200 := by rw [abs_of_nonneg hw.1]; linarith [hw'.2]
  let L := -Real.log (y 2)
  let ω := Real.exp (-2 * L / k)
  let f (z : ProjectiveState) : Fin 5 → ℝ :=
    ![|coreRadius (entranceReturnState z 0) (entranceReturnState z 2) - entranceStableRadius z|,
      |entrancePhysicalResponse z (Pi.single 0 1) - 1|,
      |entrancePhysicalResponse z (Pi.single 1 1)|,
      |entrancePhysicalResponse z (Pi.single 2 1)|,
      |entrancePhysicalResponse z (Pi.single 3 1)|]
  let g (z : ProjectiveState) : Fin 5 → ℝ :=
    ![C * (z 1 * z 2 + (z 2) ^ 2 * (z 3) ^ 2 * (θ + ω)) / k,
      C * (z 1 * z 2 + (z 2) ^ 2 * (z 3) ^ 2 * (θ + (1 + L / k) * ω)) / k ^ 2,
      C * z 2 / k, C * (z 1 + z 2 * (z 3) ^ 2),
      C * (z 1 * z 2 + (z 2) ^ 2 * z 3 * (θ + ω)) / k]
  have hfc (j : Fin 5) : ContinuousAt (fun z => f z j) y := by
    have hr := continuousAt_entrancePhysicalResponse hk hm hu' hv hw'
    fin_cases j
    · exact ((contDiffAt_entrancePhysicalReturn hk hm hu' hv hw').continuousAt.sub
        (contDiffAt_entranceStableRadius_two hM hU hW hv.1).continuousAt).abs
    · exact ((hr _).sub continuousAt_const).abs
    · exact (hr _).abs
    · exact (hr _).abs
    · exact (hr _).abs
  have hgc (j : Fin 5) : ContinuousAt (fun z => g z j) y := by
    fin_cases j <;> simp only [g, div_eq_mul_inv] <;> fun_prop
  have hp (z : ProjectiveState) (h0 : z 0 = y 0) (h2 : z 2 = y 2)
      (hu : 0 < z 1 ∧ z 1 ≤ ε) (hw : 0 < z 3 ∧ z 3 ≤ ε)
      (hθ : θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (z 1 + z 3) ^ 2 ≤ 1)) (j : Fin 5) :
      f z j ≤ g z j := by
    have hkz : 7 / 4 ≤ coreRadius (z 0) (z 2) := by simpa only [h0, h2] using hk
    have hmz : 1 ≤ z 0 := by simpa only [h0] using hm
    have hvz : 0 < z 2 ∧ z 2 < 1 := by simpa only [h2] using hv
    have huz : 0 ≤ z 1 ∧ z 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
    have hwz : 0 ≤ z 3 ∧ z 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
    obtain ⟨Φ, HΦ, _, H0, Hr, Hu, Hv, Hw⟩ := HC z θ hkz hmz hu hvz hw
      (by simpa only [h0, h2] using hθ)
    simp only [HΦ.physical_differential hkz hmz huz hvz hwz] at Hr Hu Hv Hw
    simp only [HΦ.apply_base] at H0
    fin_cases j
    · simpa [f, g, k, L, ω, entranceRadialCoordinates, h0, h2] using H0
    · simpa [f, g, k, L, ω, h0, h2] using Hr
    · simpa [f, g, k, L, ω, h0, h2] using Hu
    · simpa [f, g, k, L, ω, h0, h2] using Hv
    · simpa [f, g, k, L, ω, h0, h2] using Hw
  have Hb (j : Fin 5) : f y j ≤ g y j := by
    rcases hθ with hθ | ⟨hθ, hsmall⟩
    · exact le_of_two_nonnegative_walls_continuous hε hu hw (hfc j) (hgc j)
        (fun z h0 h2 hu hw => hp z h0 h2 hu hw (Or.inl hθ) j)
    · exact le_of_two_nonnegative_walls_quadratic hε (by linarith : 0 < k) hu hw hsmall
        (hfc j) (hgc j) (fun z h0 h2 hu hw hs => hp z h0 h2 hu hw (Or.inr ⟨hθ, hs⟩) j)
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk hy hv.1
  refine ⟨Ψ, HΨ, HΨ.physical_return_regular hk hm hu' hv hw', ?_, ?_, ?_, ?_, ?_⟩
  · change |coreRadius (entranceReturnState (Ψ (entranceRadialCoordinates y)) 0)
        (entranceReturnState (Ψ (entranceRadialCoordinates y)) 2) - entranceStableRadius y| ≤ _
    rw [HΨ.apply_base]
    exact Hb 0
  · simpa [f, g, L, ω, HΨ.physical_differential hk hm hu' hv hw'] using Hb 1
  · simpa [f, g, HΨ.physical_differential hk hm hu' hv hw'] using Hb 2
  · simpa [f, g, HΨ.physical_differential hk hm hu' hv hw'] using Hb 3
  · simpa [f, g, L, ω, HΨ.physical_differential hk hm hu' hv hw'] using Hb 4

end BianchiIX
