import BianchiIX.Dynamics.ShearRestartTailWallBounds
import BianchiIX.Dynamics.EntrancePartialCoreEntry

noncomputable section

namespace BianchiIX

open Set

/-- The tail endpoint supplies the complete small-amplitude input for an actual ascending core. -/
theorem exists_restartShearTail_core_inputs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∀ η ∈ Ioc (0 : ℝ) (1 / 10000), ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
            let k := coreRadius (Y ρ 0) (Y ρ 2)
            a ≤ 1 ∧ DifferentiableAt ℝ Y ρ ∧ 8 ≤ k ∧
            1 / (24 * a) ≤ k ∧ k ≤ 64 / a ∧ 1 < Y ρ 0 ∧
            (0 < Y ρ 1 ∧ Y ρ 1 ≤ 1 / 10000) ∧ (0 < Y ρ 2 ∧ Y ρ 2 < 1) ∧
            (0 < Y ρ 3 ∧ Y ρ 3 ≤ 1 / 10000) ∧
            Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ η / (2 * k) ∧
            Y ρ 1 ≤ 20 * h * a ^ (q - 2) ∧ Y ρ 3 ≤ 80 * a ^ (D / 2 - 1) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_entrance_inputs
  obtain ⟨hW, hhW, HW⟩ := exists_restartShearTail_wall_bounds
  refine ⟨min hI hW, lt_min hhI hhW, ?_⟩
  intro h hh q D P hq hD hP η hη
  have hq' : 2 < q := by linarith only [hq]
  have hD' : 2 < D := by linarith only [hD]
  obtain ⟨_, _, HBI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq' hD'
  obtain ⟨aI, haI, HAI⟩ := HBI P hP (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aW, haW, HAW⟩ := HW h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq' hD' hP 1 zero_lt_one
  obtain ⟨aS, haS, HAS⟩ := exists_shearTail_core_wall_scale hh.1.le hq hD hη.1
  refine ⟨min aI (min aW aS), lt_min haI (lt_min haW haS), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y k
  obtain ⟨HY, hk, hklo, hkhi, hm, hu, hv, hw, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨ha1, Hu, _, Hw, _⟩ :=
    HAW a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, Hsmall⟩ := HAS a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  change 8 ≤ k at hk
  change k ≤ 64 / a at hkhi
  have hk0 : 0 < k := by linarith only [hk]
  have Hsum : Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ η * a / 128 :=
    (add_le_add le_rfl (mul_le_of_le_one_left hw.1.le hv.2.le)).trans ((add_le_add Hu Hw).trans Hsmall)
  have Hbudget : Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ η / (2 * k) := Hsum.trans (by
    calc
      _ = η / (2 * (64 / a)) := by field_simp [ha.1.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_left hη.1.le (by positivity) (by linarith only [hkhi]))
  exact ⟨ha1, HY, hk, hklo, hkhi, hm, hu, hv, hw, Hbudget, Hu, Hw⟩

/-- The actual upward event lies on the full-core entrance, with every admissible wall power retained. -/
theorem exists_restartShearTail_core_entry :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∀ η ∈ Ioc (0 : ℝ) (1 / 10000), ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ
            let z := entranceReturnState y
            let κ := coreRadius (z 0) (z 2)
            entranceReturnValid y ∧ ContDiffAt ℝ 2 entranceReturnState y ∧
            6 ≤ κ ∧ z 2 = 1 ∧ 1 < z 0 ∧ coreRegion κ z ∧
            (0 ≤ z 1 ∧ z 1 ≤ 20 * h * a ^ (q - 2)) ∧
            (0 ≤ z 3 ∧ z 3 ≤ 80 * a ^ (D / 2 - 1)) ∧
            z 1 + z 3 ≤ η / κ ∧ projectiveCoreAngle z = -Real.arcosh κ ∧
            ∀ d : ℝ, d ≤ q - 2 → d ≤ D / 2 - 1 → z 1 + z 3 ≤ (20 * h + 80) * a ^ d := by
  obtain ⟨hstar, hhstar, HI⟩ := exists_restartShearTail_core_inputs
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP η hη
  obtain ⟨astar, hastar, HA⟩ := HI h hh q D P hq hD hP η hη
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ y z κ
  obtain ⟨ha1, _, hk, _, _, hm, hu, hv, hw, hsmall, Hu, Hw⟩ := HA a ha ε ζ ν hε hζ hν ρ hρ
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by
    change 8 ≤ coreRadius (y 0) (y 2) at hk
    linarith only [hk]
  obtain ⟨hκ, _, hhit, hmz, hreg, hU, hW, hsum, hangle⟩ :=
    entranceReturn_partialCore_entry hk hm.le ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ hη hsmall
  have HE := entranceReturn_regular hk' hm.le ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  change z 2 = 1 at hhit
  change z 1 + z 2 * z 3 ≤ η / κ at hsum
  rw [hhit, one_mul] at hsum
  have HU : z 1 ≤ 20 * h * a ^ (q - 2) := hU.2.trans Hu
  have HW : z 3 ≤ 80 * a ^ (D / 2 - 1) :=
    hW.2.trans ((mul_le_of_le_one_left hw.1.le hv.2.le).trans Hw)
  refine ⟨HE.1, HE.2.2.1, hκ, hhit, hmz, hreg, ⟨hU.1, HU⟩, ⟨hW.1, HW⟩, hsum, hangle, ?_⟩
  intro d hdq hdD
  have Hu' := Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hdq
  have Hw' := Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hdD
  exact (add_le_add HU HW).trans ((add_le_add
    (mul_le_mul_of_nonneg_left Hu' (by positivity [hh.1]))
    (mul_le_mul_of_nonneg_left Hw' (by norm_num))).trans_eq (by ring))

end BianchiIX
