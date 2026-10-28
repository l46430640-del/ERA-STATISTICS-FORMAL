import BianchiIX.Dynamics.EntranceWallDirections
import BianchiIX.Dynamics.EntranceCoreWalls
import BianchiIX.Algebra.EntranceWallCone

noncomputable section

namespace BianchiIX

/-- The actual entrance has uniform square-root weighted wall response, even as the waiting time diverges. -/
theorem exists_entrance_wall_sqrt_direction_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      let z := entranceReturnState y
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → ContDiffAt ℝ 2 entranceReturnState y ∧ 0 < z 1 ∧ 0 < z 3 ∧
      ∀ (D : ℝ) (d : ProjectiveState), 0 ≤ D → |d 0| ≤ D * k ^ 2 →
        (∀ i : Fin 4, i ≠ 0 → |d i| ≤ D * k * y i) →
        |fderiv ℝ entranceReturnState y d 1| ≤ C * D * k ^ 2 * Real.sqrt (y 1 * y 2) * Real.sqrt (z 1) ∧
        |fderiv ℝ entranceReturnState y d 3| ≤ C * D * k * Real.sqrt (y 3 * y 2) * Real.sqrt (z 3) := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_wall_direction_bounds
  refine ⟨6 * A, by positivity, ε, hε, hεsmall, ?_⟩
  intro y k z hk hm hu hv hw
  obtain ⟨HR, hU, hW, HD⟩ := HA y hk hm hu hv hw
  have Hdecay := entranceReturn_decay hk hm ⟨hu.1.le, hu.2.trans hεsmall⟩ hv ⟨hw.1.le, hw.2.trans hεsmall⟩
  refine ⟨HR, hU, hW, ?_⟩
  intro D d hD hd0 hdwall
  obtain ⟨HU, HW⟩ := HD D d hD hd0 hdwall
  obtain ⟨HU', HW'⟩ := entrance_wall_sqrt_response hA.le hD (by linarith only [hk])
    (neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)) hu.1.le hv.1.le hw.1.le hU.le hW.le
    Hdecay.1 Hdecay.2 HU HW
  refine ⟨HU', HW'.trans ?_⟩
  have hk0 : 0 ≤ k := by linarith only [hk]
  gcongr
  linarith only [hA]

/-- The bounds are ordinary derivatives on a differentiable curve, including moving active-wall data. -/
theorem exists_entrance_wall_sqrt_curve_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (Y : ℝ → ProjectiveState) (ρ D : ℝ),
      let y := Y ρ
      let k := coreRadius (y 0) (y 2)
      let Z := fun t => entranceReturnState (Y t)
      DifferentiableAt ℝ Y ρ → 0 ≤ D → 7 / 4 ≤ k → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ ε) →
      |deriv (fun t => Y t 0) ρ| ≤ D * k ^ 2 →
      (∀ i : Fin 4, i ≠ 0 → |deriv (fun t => Y t i) ρ| ≤ D * k * y i) →
      DifferentiableAt ℝ Z ρ ∧ 0 < Z ρ 1 ∧ 0 < Z ρ 3 ∧
      |deriv (fun t => Z t 1) ρ| ≤ C * D * k ^ 2 * Real.sqrt (y 1 * y 2) * Real.sqrt (Z ρ 1) ∧
      |deriv (fun t => Z t 3) ρ| ≤ C * D * k * Real.sqrt (y 3 * y 2) * Real.sqrt (Z ρ 3) := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_wall_sqrt_direction_bounds
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro Y ρ D y k Z HY hD hk hm hu hv hw hd0 hdwall
  obtain ⟨HR, hU, hW, HD⟩ := HC y hk hm hu hv hw
  have HZ := (HR.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt ρ HY.hasDerivAt
  change HasDerivAt Z _ ρ at HZ
  have hi (i : Fin 4) : deriv Y ρ i = deriv (fun t => Y t i) ρ := (hasDerivAt_pi.mp HY.hasDerivAt i).deriv.symm
  have HG := HD D (deriv Y ρ) hD (by simpa only [hi] using hd0)
    (fun i hn => by simpa only [hi] using hdwall i hn)
  refine ⟨HZ.differentiableAt, hU, hW, ?_⟩
  rw [(hasDerivAt_pi.mp HZ 1).deriv, (hasDerivAt_pi.mp HZ 3).deriv]
  exact HG

end BianchiIX
