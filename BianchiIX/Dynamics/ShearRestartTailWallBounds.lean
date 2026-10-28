import BianchiIX.Dynamics.ShearRestartTailEntranceInputs
import BianchiIX.Analysis.ShearTailWallSmallness

noncomputable section

namespace BianchiIX

open Set

/-- Exact endpoint powers also make the logarithmically weighted square-root wall budget arbitrarily small. -/
theorem exists_restartShearTail_wall_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 2 < D → 6 * D + 2 < P → ∀ δ > (0 : ℝ),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ
          a ≤ 1 ∧ y 1 ≤ 20 * h * a ^ (q - 2) ∧
          y 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧ y 3 ≤ 80 * a ^ (D / 2 - 1) ∧
          (1 + |Real.log a|) * Real.sqrt (y 1 + y 3) ≤ δ := by
  obtain ⟨hstar, hhstar, HV⟩ := exists_restartShearTail_control
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP δ hδ
  obtain ⟨aV, haV, HAV⟩ := HV h hh q D P hq (by linarith only [hD]) hP
  obtain ⟨aS, haS, HAS⟩ := exists_shearTail_sqrt_wall_scale hh.1.le hq hD hδ
  refine ⟨min aV aS, lt_min haV haS, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ y
  obtain ⟨_, _, _, _, _, _, Hu, Hv, Hw⟩ :=
    HAV a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε
      ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  change y 1 ≤ 20 * h * a ^ (q - 2) at Hu
  change y 2 ≤ 40 * ζ * a ^ (-6 * D - 2) at Hv
  change y 3 ≤ 80 * ε * a ^ (D / 2 - 1) at Hw
  have Hw' : y 3 ≤ 80 * a ^ (D / 2 - 1) := Hw.trans (by
    have H := mul_le_mul_of_nonneg_right (show ε ≤ 1 by linarith only [hε.2])
      (by positivity [ha.1] : 0 ≤ 80 * a ^ (D / 2 - 1))
    nlinarith only [H])
  obtain ⟨ha1, Hsmall⟩ := HAS a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩
  exact ⟨ha1, Hu, Hv, Hw', (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (add_le_add Hu Hw')) (by positivity)).trans Hsmall⟩

end BianchiIX
