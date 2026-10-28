import BianchiIX.Dynamics.CoreTailMultipliers

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- B.45 with actual positive factors, bounded inverses, and two bounded logarithmic derivatives. -/
theorem exists_compact_tail_multiplier_bounds {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (coreTailState η) Y ∧
        projectiveReflection (coreTailState η Y) =
          ![-coreTailState η Y 0, Y 1 * coreTailMultiplier η Y 0, Y 2 * coreTailMultiplier η Y 1, η] ∧
        ∀ i : Fin 2, 0 < coreTailMultiplier η Y i ∧
          ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier η Z i)) Y ∧
          coreTailMultiplier η Y i + (coreTailMultiplier η Y i)⁻¹ +
            ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y‖ +
            ‖fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y‖ ≤ C := by
  obtain ⟨ε, hε, _, _, Htail⟩ := exists_compact_connection_tail hη
  let S : Set CoreAngleState := Icc (![31 / 8, -ε, -ε] : CoreAngleState) ![6, ε, ε]
  have hcompact : IsCompact S := isCompact_Icc
  have hcoords {Y : CoreAngleState} (hY : Y ∈ S) :
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) ∧ |Y 1| ≤ ε ∧ |Y 2| ≤ ε :=
    ⟨⟨hY.1 0, hY.2 0⟩, abs_le.mpr ⟨hY.1 1, hY.2 1⟩, abs_le.mpr ⟨hY.1 2, hY.2 2⟩⟩
  have hreg {Y : CoreAngleState} (hY : Y ∈ S) (i : Fin 2) :
      ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
        ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier η Z i)) Y := by
    have hbox := hcoords hY
    have HY := Htail Y hbox.1 hbox.2.1 hbox.2.2
    exact contDiffAt_coreTailMultiplier_two (by linarith only [hbox.1.1]) HY.1 HY.2.1 i
  let q : CoreAngleState → Fin 2 → ℝ := fun Y i =>
    coreTailMultiplier η Y i + (coreTailMultiplier η Y i)⁻¹ +
      ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y‖ +
      ‖fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y‖
  have hcq (i : Fin 2) : ContinuousOn (fun Y => q Y i) S := by
    intro Y hY
    obtain ⟨hb, hl⟩ := hreg hY i
    have hl' := hl.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact (((hb.continuousAt.add (hb.inv (coreTailMultiplier_pos η Y i).ne').continuousAt).add
      (hl.continuousAt_fderiv (by norm_num)).norm).add
      (hl'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  have hcmax : ContinuousOn (fun Y => max (q Y 0) (q Y 1)) S :=
    (continuous_fst.max continuous_snd).comp_continuousOn ((hcq 0).prodMk (hcq 1))
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hcmax
  refine ⟨ε, hε, max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Y hk hu hw
  have hY : Y ∈ S := by
    constructor
    · intro i
      fin_cases i
      · exact hk.1
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · intro i
      fin_cases i
      · exact hk.2
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have HY := Htail Y hk hu hw
  refine ⟨HY.1, HY.2.1, HY.2.2.1, coreTail_reflected_multiplier_state HY.1, ?_⟩
  intro i
  refine ⟨coreTailMultiplier_pos η Y i, (hreg hY i).1, (hreg hY i).2, ?_⟩
  have H : max (q Y 0) (q Y 1) ≤ max B 1 :=
    (le_abs_self _).trans ((hB Y hY).trans (le_max_left _ _))
  fin_cases i
  · exact (le_max_left _ _).trans H
  · exact (le_max_right _ _).trans H

end BianchiIX
