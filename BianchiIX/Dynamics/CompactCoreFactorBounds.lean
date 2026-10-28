import BianchiIX.Dynamics.CompactCoreFactors

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

/-- Positive compact-core factors have a common strict contraction and bounded logarithmic derivatives. -/
theorem exists_compact_core_factor_bounds :
    ∃ ε > (0 : ℝ), ∃ q > (0 : ℝ), q < 1 ∧ ∃ C > (0 : ℝ),
      ∀ Y : CoreAngleState, (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
          ∀ i : Fin 2,
            coreReturnState coreRadiusReturnTime Y i.succ = Y i.succ * compactCoreFactor Y i ∧
            0 < compactCoreFactor Y i ∧ compactCoreFactor Y i ≤ q ∧
            ContDiffAt ℝ 1 (fun Z => compactCoreFactor Z i) Y ∧
            ContDiffAt ℝ 1 (fun Z => Real.log (compactCoreFactor Z i)) Y ∧
            ‖fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y‖ ≤ C ∧
            (∀ᶠ Z in 𝓝 Y, coreReturnState coreRadiusReturnTime Z i.succ = Z i.succ * compactCoreFactor Z i) := by
  let S : Set CoreAngleState := (fun k : ℝ => (![k, 0, 0] : CoreAngleState)) '' Icc 2 6
  have hS : IsCompact S := isCompact_Icc.image (by fun_prop)
  have hSne : S.Nonempty := ⟨![2, 0, 0], 2, by norm_num, rfl⟩
  have hreg (Y : CoreAngleState) (hY : Y ∈ S) (i : Fin 2) :
      ContDiffAt ℝ 1 (fun Z => compactCoreFactor Z i) Y ∧
        0 < compactCoreFactor Y i ∧ compactCoreFactor Y i < 1 := by
    obtain ⟨k, hk, rfl⟩ := hY
    have hk1 : 1 < k := by linarith only [hk.1]
    exact ⟨contDiffAt_compactCoreFactor_reference hk1 i, compactCoreFactor_reference_bounds hk1 i⟩
  have hc (i : Fin 2) : ContinuousOn (fun Y => compactCoreFactor Y i) S :=
    fun Y hY => (hreg Y hY i).1.continuousAt.continuousWithinAt
  have hcmax : ContinuousOn (fun Y => max (compactCoreFactor Y 0) (compactCoreFactor Y 1)) S :=
    (continuous_fst.max continuous_snd).comp_continuousOn ((hc 0).prodMk (hc 1))
  obtain ⟨Z, hZS, hmax⟩ := hS.exists_isMaxOn hSne hcmax
  let q₀ := max (compactCoreFactor Z 0) (compactCoreFactor Z 1)
  have hq₀ : 0 < q₀ := lt_of_lt_of_le (hreg Z hZS 0).2.1 (le_max_left _ _)
  have hq₀1 : q₀ < 1 := max_lt (hreg Z hZS 0).2.2 (hreg Z hZS 1).2.2
  let q := (q₀ + 1) / 2
  have hq : 0 < q := by dsimp [q]; linarith only [hq₀]
  have hq1 : q < 1 := by dsimp [q]; linarith only [hq₀1]
  have hq₀q : q₀ < q := by dsimp [q]; linarith only [hq₀1]
  have hbound (Y : CoreAngleState) (hY : Y ∈ S) (i : Fin 2) : compactCoreFactor Y i < q := by
    apply lt_of_le_of_lt _ hq₀q
    have H := hmax hY
    fin_cases i
    · exact (le_max_left _ _).trans H
    · exact (le_max_right _ _).trans H
  let G : Set CoreAngleState := {Y | ∀ i : Fin 2,
    ContDiffAt ℝ 1 (fun Z => compactCoreFactor Z i) Y ∧
      0 < compactCoreFactor Y i ∧ compactCoreFactor Y i < q}
  have hSG : S ⊆ interior G := by
    intro Y hY
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.eventually_all.mpr
    intro i
    obtain ⟨hdi, hpos, _⟩ := hreg Y hY i
    exact (hdi.eventually (by norm_num)).and
      ((hdi.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)).and
        (hdi.continuousAt.eventually (isOpen_Iio.mem_nhds (hbound Y hY i))))
  obtain ⟨δ, hδ, hδG⟩ := hS.exists_cthickening_subset_open isOpen_interior hSG
  let W := cthickening δ S
  have hWG : W ⊆ G := hδG.trans interior_subset
  have hlog (Y : CoreAngleState) (hY : Y ∈ W) (i : Fin 2) :
      ContDiffAt ℝ 1 (fun Z => Real.log (compactCoreFactor Z i)) Y :=
    (hWG hY i).1.log (ne_of_gt (hWG hY i).2.1)
  let b : CoreAngleState → ℝ := fun Y =>
    ‖fderiv ℝ (fun Z => Real.log (compactCoreFactor Z 0)) Y‖ +
      ‖fderiv ℝ (fun Z => Real.log (compactCoreFactor Z 1)) Y‖
  have hcb : ContinuousOn b W := fun Y hY =>
    (((hlog Y hY 0).continuousAt_fderiv (by norm_num)).norm.add
      ((hlog Y hY 1).continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨B, hB⟩ := hS.cthickening.exists_bound_of_continuousOn hcb
  obtain ⟨ε₀, hε₀, hfactor⟩ := exists_compact_core_factorization
  let ε := min ε₀ δ
  refine ⟨ε, lt_min hε₀ hδ, q, hq, hq1, max B 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro Y hk hu hw
  have hY := hfactor Y hk (hu.trans (min_le_left _ _)) (hw.trans (min_le_left _ _))
  have hdist : dist Y (![Y 0, 0, 0] : CoreAngleState) ≤ δ := by
    apply (dist_pi_le_iff hδ.le).mpr
    intro i
    fin_cases i
    · simpa using hδ.le
    · simpa [Real.dist_eq] using hu.trans (min_le_right ε₀ δ)
    · simpa [Real.dist_eq] using hw.trans (min_le_right ε₀ δ)
  have hYW : Y ∈ W := mem_cthickening_of_dist_le Y _ δ S ⟨Y 0, hk, rfl⟩ hdist
  refine ⟨hY.1, hY.2.1, ?_⟩
  intro i
  refine ⟨(hY.2.2 i).2.1, (hWG hYW i).2.1, (hWG hYW i).2.2.le,
    (hWG hYW i).1, hlog Y hYW i, ?_, (hY.2.2 i).2.2⟩
  have H : b Y ≤ max B 1 := (le_abs_self _).trans ((hB Y hYW).trans (le_max_left _ _))
  fin_cases i
  · exact (le_add_of_nonneg_right (norm_nonneg _)).trans H
  · exact (le_add_of_nonneg_left (norm_nonneg _)).trans H

end BianchiIX
