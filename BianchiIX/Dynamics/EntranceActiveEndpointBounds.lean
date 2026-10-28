import BianchiIX.Dynamics.EntranceActiveEndpoint
import BianchiIX.Dynamics.EntranceActiveResponse
import BianchiIX.Analysis.EntranceTransportWeights

noncomputable section

namespace BianchiIX

open Set

/-- The terminal growth rates remove the moving-exit contribution uniformly in the
active input, including arbitrarily long waiting times. -/
theorem exists_entrance_active_endpoint_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ (y : ProjectiveState),
      7 / 4 ≤ coreRadius (y 0) (y 2) → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ ε) →
      coreRadius (y 0) (y 2) ^ 2 * (y 1 + y 3) ≤ 1 →
      ∀ (Ψ : ProjectiveState → ProjectiveState), EntranceRadialInverseAt y Ψ →
      let k := coreRadius (y 0) (y 2)
      let z := entranceRadialCoordinates y
      let Y := entranceReturnState y
      let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
      let L := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
      let H := y 1 * y 2 + (y 2 * y 3) ^ 2 / k ^ 2
      |y 2 * fderiv ℝ Q z (Pi.single 2 1) + entranceRadialDrift Y| ≤ C * H / k ∧
        |y 2 * fderiv ℝ L z (Pi.single 2 1) 0 + entranceStrongLogRate Y| +
          k ^ 2 * |y 2 * fderiv ℝ L z (Pi.single 2 1) 1 + entranceWeakLogRate Y| ≤ C / k := by
  obtain ⟨C, hC, ε, hε, hεcap, HC⟩ := exists_entrance_return_active_response
  refine ⟨3 * C, by positivity, ε, hε, hεcap, ?_⟩
  intro y hk hm hu hv hw hsmall Ψ HΨ k z Y Q L H
  have hu' : 0 < y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1, hu.2.trans hεcap⟩
  have hw' : 0 < y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hεcap⟩
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) :=
    ⟨(entranceReturn_regular hk hm ⟨hu'.1.le, hu'.2⟩ hv ⟨hw'.1.le, hw'.2⟩).1.1.1.1.le, le_rfl⟩
  have hresponse := HC y hk hm hu hv hw hsmall _ ht
  dsimp only at hresponse
  change _ ≤ C * H / k ∧ _ ≤ C * (1 + (Real.log (Y 2) - Real.log (y 2)) * H) / k at hresponse
  have hhit : Y 2 = 1 := (entranceReturn_active_component hk hm ⟨hu'.1.le, hu'.2⟩ hv ⟨hw'.1.le, hw'.2⟩).1
  rw [hhit, Real.log_one, zero_sub] at hresponse
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hH : 0 ≤ H := by dsimp [H]; positivity [hu.1, hv.1]
  have hθ : 0 ≤ 1 / k ^ 2 ∧ 1 / k ^ 2 ≤ 1 :=
    ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hwait := (entrance_phase_waiting_budget hu.1.le ⟨hv.1, hv.2.le⟩
    ⟨hw.1.le, by linarith [hw'.2]⟩ hθ).2.2
  have hLH : (-Real.log (y 2)) * H ≤ 2 := by
    simp only [one_div_mul_eq_div] at hwait
    exact hwait.trans (by linarith [hu'.2, hw'.2])
  have HE := HΨ.return_active_endpoint hk hm hu' hv hw' 1
  dsimp only at HE
  change y 2 * fderiv ℝ Q z (Pi.single 2 1) + entranceRadialDrift Y = _ ∧
    y 2 • fderiv ℝ L z (Pi.single 2 1) + _ = _ at HE
  constructor
  · rw [HE.1]
    exact hresponse.1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ 3 * C) hH) hk0.le)
  · have hU := congrFun HE.2 0
    have hW := congrFun HE.2 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_pow, one_mul, entranceWallTangent] at hU hW
    rw [hU, hW]
    have hbound := hresponse.2
    simp only [entranceWallTangent, Matrix.cons_val_zero, Matrix.cons_val_one,
      abs_mul, abs_sq] at hbound
    have hnum : C * (1 + (-Real.log (y 2)) * H) ≤ 3 * C := by nlinarith only [hLH, hC]
    exact hbound.trans (div_le_div_of_nonneg_right hnum hk0.le)

end BianchiIX
