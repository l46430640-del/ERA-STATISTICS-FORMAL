import BianchiIX.Dynamics.TaubArcPropagation
import BianchiIX.Dynamics.TaubSectionLimit

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def primaryAxisArc (i : Fin 3) (q : ℝ) : NormalizedState :=
  (primaryAxisFrame i).map.symm (taubBoundaryArc q)

theorem mainWallBoundary_eq_taubBoundaryArc {h : ℝ} (hh : 0 ≤ h) (hhmax : h ≤ 1) :
    mainWallBoundary h = taubBoundaryArc (Real.sqrt (1 - h ^ 2)) := by
  have hrad : 0 ≤ 1 - h ^ 2 := by nlinarith only [hh, hhmax]
  ext j
  fin_cases j <;> simp [mainWallBoundary, taubBoundaryArc, Real.sq_sqrt hrad, Real.sqrt_sq hh]

theorem primaryAxisArc_coordinates (i : Fin 3) (q : ℝ) :
    normalizedShears (primaryAxisArc i q) = (fun j => q * normalizedShears (taubPoint i) j) ∧
    normalizedWalls (primaryAxisArc i q) = (fun j => if j = i then Real.sqrt (1 - q ^ 2) else 0) := by
  have hmap : (primaryAxisFrame i).map (primaryAxisArc i q) = taubBoundaryArc q :=
    (primaryAxisFrame i).map.apply_symm_apply _
  constructor
  · ext j
    have H := congrArg (fun z => normalizedShears z ((Equiv.swap 0 i) j)) hmap
    simp only [primaryAxisFrame, axisPermutation_shears, Equiv.swap_apply_self] at H
    rw [H, normalizedShears_taubPoint]
    fin_cases i <;> fin_cases j <;>
      simp [taubBoundaryArc, normalizedShears, Equiv.swap_apply_def] <;> ring
  · ext j
    have H := congrArg (fun z => normalizedWalls z ((Equiv.swap 0 i) j)) hmap
    simp only [primaryAxisFrame, axisPermutation_walls, Equiv.swap_apply_self] at H
    rw [H]
    fin_cases i <;> fin_cases j <;> simp [taubBoundaryArc, normalizedWalls, Equiv.swap_apply_def]

theorem primaryAxisArc_endpoints (i : Fin 3) :
    primaryAxisArc i (-1) = -taubPoint i ∧ primaryAxisArc i 1 = taubPoint i := by
  have hm : taubBoundaryArc (-1) = -taubPoint 0 := by
    ext j
    fin_cases j <;> simp [taubBoundaryArc, taubPoint]
  have hp : taubBoundaryArc 1 = taubPoint 0 := by
    ext j
    fin_cases j <;> simp [taubBoundaryArc, taubPoint]
  constructor
  · apply (primaryAxisFrame i).map.injective
    change (primaryAxisFrame i).map ((primaryAxisFrame i).map.symm (taubBoundaryArc (-1))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, hm, map_neg, primaryAxisFrame_taubPoint]
  · apply (primaryAxisFrame i).map.injective
    change (primaryAxisFrame i).map ((primaryAxisFrame i).map.symm (taubBoundaryArc 1)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, hp, primaryAxisFrame_taubPoint]

theorem primaryAxisArc_closed_mem_omegaLimit_of_boundary (i : Fin 3)
    {x : NormalizedState} {h : ℝ} (hc : stateConstraint x = 1) (hh : 0 < h) (hhmax : h < 1)
    (hz : primaryAxisBoundary i h ∈ normalizedOmegaLimit x) :
    ∀ q ∈ Icc (-1 : ℝ) 1, primaryAxisArc i q ∈ normalizedOmegaLimit x := by
  have hrad : 0 < 1 - h ^ 2 := by nlinarith only [hh, hhmax]
  have hq : Real.sqrt (1 - h ^ 2) ∈ Ioo (-1 : ℝ) 1 := by
    constructor <;> nlinarith [Real.sqrt_nonneg (1 - h ^ 2), Real.sq_sqrt hrad.le, sq_pos_of_pos hh]
  have hcA := ((primaryAxisFrame i).constraint x).trans hc
  have hstart := normalizedOmegaLimit_symmetry (primaryAxisFrame i) hc hz
  change (primaryAxisFrame i).map ((primaryAxisFrame i).map.symm (mainWallBoundary h)) ∈ _ at hstart
  rw [ContinuousLinearEquiv.apply_symm_apply, mainWallBoundary_eq_taubBoundaryArc hh.le hhmax.le] at hstart
  intro q hq'
  have H := taubBoundaryArc_closed_mem_omegaLimit hcA hq hstart q hq'
  have Hback := normalizedOmegaLimit_symmetry (primaryAxisFrame i).symm hcA H
  change (primaryAxisFrame i).map.symm (taubBoundaryArc q) ∈
    normalizedOmegaLimit ((primaryAxisFrame i).map.symm ((primaryAxisFrame i).map x)) at Hback
  rw [ContinuousLinearEquiv.symm_apply_apply] at Hback
  exact Hback

theorem taubPoint_mem_omegaLimit_of_boundary (i : Fin 3)
    {x : NormalizedState} {h : ℝ} (hc : stateConstraint x = 1) (hh : 0 < h) (hhmax : h < 1)
    (hz : primaryAxisBoundary i h ∈ normalizedOmegaLimit x) :
    taubPoint i ∈ normalizedOmegaLimit x := by
  have H := primaryAxisArc_closed_mem_omegaLimit_of_boundary i hc hh hhmax hz 1 (by constructor <;> norm_num)
  rwa [(primaryAxisArc_endpoints i).2] at H

/-- The exact equivalence between a Taub limit point and convergent crossings of its fixed physical section. -/
theorem taubPoint_mem_omegaLimit_iff_section_limit (i : Fin 3) {x : NormalizedState} {h d : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hr : 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x))
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hprod : ∀ j k : Fin 3, j ≠ k → Tendsto
      (fun t => wallValue j (normalizedMaxCurve x 0 t) * wallValue k (normalizedMaxCurve x 0 t)) atTop (𝓝 0)) :
    taubPoint i ∈ normalizedOmegaLimit x ↔
      ∃ c : ℕ → ℝ, Tendsto c atTop atTop ∧
        Tendsto (fun n => normalizedMaxCurve x 0 (c n)) atTop (𝓝 (primaryAxisBoundary i h)) ∧
        ∀ n, 0 < c n ∧ c n ∈ normalizedMaxDomain x 0 ∧
          ∃ y ∈ mainWallChartDomain h, axisWallChart (primaryAxisFrame i) h y = normalizedMaxCurve x 0 (c n) ∧
            |y 0| < d ∧ Real.exp (-y 1) < d ∧ Real.exp (-y 2) < d := by
  constructor
  · exact exists_primaryAxis_section_limit i hc hp hr hh hhmax hd hdh hprod
  · rintro ⟨c, ht, hz, _⟩
    exact taubPoint_mem_omegaLimit_of_boundary i hc hh (hhmax.trans_lt (by norm_num))
      (mem_normalizedOmegaLimit_of_sequence ht hz)

theorem primaryAxisArc_closed_mem_omegaLimit_of_taub (i : Fin 3) {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hr : 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x))
    (hprod : ∀ j k : Fin 3, j ≠ k → Tendsto
      (fun t => wallValue j (normalizedMaxCurve x 0 t) * wallValue k (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    (hz : taubPoint i ∈ normalizedOmegaLimit x) :
    ∀ q ∈ Icc (-1 : ℝ) 1, primaryAxisArc i q ∈ normalizedOmegaLimit x := by
  have H := primaryAxisBoundary_mem_omegaLimit i (h := 1 / 32) (d := 1 / 1024)
    hc hp hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) hprod hz
  exact primaryAxisArc_closed_mem_omegaLimit_of_boundary i hc (by norm_num) (by norm_num) H

theorem closure_primaryAxisArc_subset_omegaLimit (i : Fin 3) {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hr : 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x))
    (hprod : ∀ j k : Fin 3, j ≠ k → Tendsto
      (fun t => wallValue j (normalizedMaxCurve x 0 t) * wallValue k (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    (hz : taubPoint i ∈ normalizedOmegaLimit x) :
    closure (primaryAxisArc i '' Ioo (-1 : ℝ) 1) ⊆ normalizedOmegaLimit x := by
  apply closure_minimal _ (isClosed_normalizedOmegaLimit x)
  rintro _ ⟨q, hq, rfl⟩
  exact primaryAxisArc_closed_mem_omegaLimit_of_taub i hc hp hr hprod hz q (Ioo_subset_Icc_self hq)

end BianchiIX
