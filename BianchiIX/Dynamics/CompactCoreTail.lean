import BianchiIX.Dynamics.CoreTail
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- A fixed tail height gives one wall neighborhood and uniform bounds on each compact phase range. -/
theorem exists_compact_core_tail_two_germ {a b η : ℝ} (ha : 1 < a) (hη : 0 < η ∧ η < 1) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (a ≤ Y 0 ∧ Y 0 ≤ b) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (coreTailState η) Y ∧
        |coreTailTime η Y| + ‖coreTailState η Y‖ +
          ‖fderiv ℝ (coreTailTime η) Y‖ + ‖fderiv ℝ (coreTailState η) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreTailTime η)) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreTailState η)) Y‖ ≤ C ∧
        (∀ᶠ Z in 𝓝 Y, coreTailValid η Z ∧ ContDiffAt ℝ 2 (coreTailTime η) Z ∧
          ContDiffAt ℝ 2 (coreTailState η) Z) := by
  let T := coreTailTime η
  let P := coreTailState η
  let G : Set CoreAngleState := {Y | coreTailValid η Y ∧ ContDiffAt ℝ 2 T Y ∧ ContDiffAt ℝ 2 P Y}
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc a b
  have hcS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSG : S ⊆ interior G := by
    rintro Y ⟨k, hk, rfl⟩
    obtain ⟨_, _, ht, hP, hvalid⟩ := coreTail_reference_regular (ha.trans_le hk.1) hη
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hvalid, ht.eventually (by norm_num), hP.eventually (by norm_num)] with Z hz htZ hPZ
    exact ⟨hz, htZ, hPZ⟩
  obtain ⟨ε, hε, hεG⟩ := hcS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening ε S
  have hWG : W ⊆ G := hεG.trans interior_subset
  let q : CoreAngleState → ℝ := fun Y => |T Y| + ‖P Y‖ + ‖fderiv ℝ T Y‖ +
    ‖fderiv ℝ P Y‖ + ‖fderiv ℝ (fderiv ℝ T) Y‖ + ‖fderiv ℝ (fderiv ℝ P) Y‖
  have hcq : ContinuousOn q W := by
    intro Y hY
    obtain ⟨_, ht, hP⟩ := hWG hY
    have ht' := ht.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hP' := hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact (((((ht.continuousAt.abs.add hP.continuousAt.norm).add
      (ht.continuousAt_fderiv (by norm_num)).norm).add
      (hP.continuousAt_fderiv (by norm_num)).norm).add
      (ht'.continuousAt_fderiv (by norm_num)).norm).add
      (hP'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hcS.cthickening.exists_bound_of_continuousOn hcq
  refine ⟨ε, hε, max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Y hk hu hw
  have hdist : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ ε := by
    apply (dist_pi_le_iff hε.le).mpr
    intro i
    fin_cases i
    · simpa using hε.le
    · simpa [Real.dist_eq] using hu
    · simpa [Real.dist_eq] using hw
  have hYS : (![Y 0, 0, 0] : CoreAngleState) ∈ S := ⟨Y 0, hk, rfl⟩
  have hYW : Y ∈ W := mem_cthickening_of_dist_le Y _ ε S hYS hdist
  obtain ⟨hvalid, ht, hP⟩ := hWG hYW
  exact ⟨hvalid, ht, hP, (le_abs_self (q Y)).trans ((hB Y hYW).trans (le_max_left _ _)),
    mem_interior_iff_mem_nhds.mp (hεG hYW)⟩

/-- The compact-connection range of B.7 has an actual finite downward tail with uniform C2 bounds. -/
theorem exists_compact_connection_tail {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (coreTailState η) Y ∧
        |coreTailTime η Y| + ‖coreTailState η Y‖ +
          ‖fderiv ℝ (coreTailTime η) Y‖ + ‖fderiv ℝ (coreTailState η) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreTailTime η)) Y‖ +
          ‖fderiv ℝ (fderiv ℝ (coreTailState η)) Y‖ ≤ C := by
  obtain ⟨ε, hε, C, hC, H⟩ := exists_compact_core_tail_two_germ (a := 31 / 8) (b := 6)
    (by norm_num) ⟨hη.1, by linarith only [hη.2]⟩
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  have HY := H Y hk hu hw
  exact ⟨HY.1, HY.2.1, HY.2.2.1, HY.2.2.2.1⟩

end BianchiIX
