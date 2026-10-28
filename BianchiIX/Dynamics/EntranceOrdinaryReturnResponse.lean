import BianchiIX.Dynamics.EntranceRadialReturnDifferential
import BianchiIX.Dynamics.EntrancePhaseResponse
import BianchiIX.Analysis.EntranceOrdinaryWeights

noncomputable section

namespace BianchiIX

open Set

/-- The phase and logarithmic wall response for the true first arrival in ordinary radial coordinates. -/
theorem exists_entrance_ordinary_return_response :
    ∃ T > (0 : ℝ), ∃ K > (0 : ℝ), ∃ F > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∀ (Ψ : ProjectiveState → ProjectiveState), EntranceRadialInverseAt y Ψ →
      ∀ (d : ProjectiveState), d 2 = 0 →
      let z := entranceRadialCoordinates y
      let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
      let L := fun z => entranceLogWalls k (entranceReturnState (Ψ z))
      let J := y 2 * |d 1| + (y 1 * y 2 + θ * (y 2) ^ 2 * y 3) * |d 3|
      let H := y 1 * y 2 + θ * (y 2 * y 3) ^ 2
      |fderiv ℝ Q z d - d 0| ≤ 2 * (K * J / k) + 2 * (F * H / k ^ 2) * |d 0| ∧
      |fderiv ℝ L z d 0 - d 1 / y 1| + |fderiv ℝ L z d 1 - k ^ 2 * (d 3 / y 3)| ≤
        T * (|d 1| + |d 3| + 2 * (-Real.log (y 2)) * (|d 0| + K * J / k)) := by
  obtain ⟨T, hT, K, hK, F, hF, ε₀, hε₀, HP⟩ := exists_actual_entrance_phase_response
  let ε := min ε₀ (1 / 10000)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  refine ⟨T, hT, K, hK, F, hF, ε, hε, min_le_right _ _, ?_⟩
  intro y θ k hk hm hu hv hw hθ Ψ HΨ d hd2 z Q L J H
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans (min_le_right _ _)⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans (min_le_right _ _)⟩
  have hD := entrance_initial_denom_pos hk hm hu' hv hw'
  have HR := entranceReturn_regular hk hm hu' hv hw'
  let t := entranceReturnTime y
  have ht : 0 ≤ t := HR.1.1.1.1.le
  have hreg := entranceReturn_region hk hm hu' hv hw'
  have hpos := entranceReturn_walls_pos hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩
  have hinit : projectiveOriginalFlow y 0 0 = y := projectiveOriginalFlow_initial hD 0
  have hy : entranceRegion k y := by simpa only [hinit] using hreg 0 ⟨le_rfl, ht⟩
  let w := entranceRadialInverseDifferential y d
  have hw1 : w 1 = d 1 := by simp [w, entranceRadialInverseDifferential_apply]
  have hw2 : w 2 = 0 := by simpa [w, entranceRadialInverseDifferential_apply] using hd2
  have hw3 : w 3 = d 3 := by simp [w, entranceRadialInverseDifferential_apply]
  have hZ0 : fderiv ℝ entranceStableRadius y w = d 0 := entranceRadialInverseDifferential_radius hk hy hv.1 d
  have HP' := HP y 0 0 t k θ hD hk ht (fun r hr => (HR.1.2.1 r hr).1)
    (fun r hr => (HR.1.2.1 r hr).2) hreg (fun r hr => (hpos r hr).2.1)
    (fun r hr => ⟨(hpos r hr).1.ne', (hpos r hr).2.2.ne'⟩)
    (by rw [hinit]; exact hu.2.trans (min_le_left _ _))
    (by rw [hinit]; exact hw.2.trans (min_le_left _ _))
    (by simpa only [hinit] using hθ) w hw2
  have HT := HP'.2.2 t ⟨ht, le_rfl⟩
  dsimp only at HT
  simp only [hinit, entranceProjectedFlowVariation_initial hD, hw1, hw3, hZ0] at HT
  obtain ⟨hweights, hsource⟩ := entrance_ordinary_initial_weights hu.1 hw.1 (y 2) θ (d 1) (d 3)
  have hhit : projectiveOriginalFlow y 0 t 2 = 1 := (entranceReturn_active_component hk hm hu' hv hw').1
  rw [hweights, hsource, hhit, Real.log_one, zero_sub] at HT
  have hQ : fderiv ℝ Q z d = fderiv ℝ entranceStableRadius (entranceReturnState y)
      (entranceRadialClockVariation y 0 t d) := by
    have HE := HΨ.return_radius_differential hk hm hu' hv hw' d
    simpa only [hd2, zero_div, zero_mul, sub_zero] using HE
  have hL : fderiv ℝ L z d = entranceWallTangent k (entranceReturnState y)
      (entranceRadialClockVariation y 0 t d) :=
    HΨ.return_logWalls_differential hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ d hd2
  constructor
  · rw [hQ]
    exact HT.1
  · rw [hL]
    change |entranceRadialClockVariation y 0 t d 1 / entranceReturnState y 1 - d 1 / y 1| +
      |k ^ 2 * (entranceRadialClockVariation y 0 t d 3 / entranceReturnState y 3) - k ^ 2 * (d 3 / y 3)| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg k)]
    exact HT.2.2

end BianchiIX
