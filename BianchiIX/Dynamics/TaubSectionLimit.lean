import BianchiIX.Dynamics.LateAxisCrossing
import BianchiIX.Dynamics.MainWallBoundary
import BianchiIX.Dynamics.NormalizedOmegaLimit

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Approach to the primary Taub point produces actual section crossings converging to its single-wall boundary point. -/
theorem exists_taub_section_limit {x : NormalizedState} {h d : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x) (hr : 0 < normalizedTaubRadiusSq x)
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hprod : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    (hvisit : taubPoint 0 ∈ normalizedOmegaLimit x) :
    ∃ c : ℕ → ℝ, Tendsto c atTop atTop ∧
      Tendsto (fun n => normalizedMaxCurve x 0 (c n)) atTop (𝓝 (mainWallBoundary h)) ∧
      ∀ n, 0 < c n ∧ c n ∈ normalizedMaxDomain x 0 ∧
        ∃ y ∈ mainWallChartDomain h, mainWallChart h y = normalizedMaxCurve x 0 (c n) ∧
          |y 0| < d ∧ Real.exp (-y 1) < d ∧ Real.exp (-y 2) < d := by
  have H := exists_arbitrarily_late_taub_section_crossing hc hp hr hh hhmax hd hdh hprod
    (normalizedOmegaLimit_late_visit hvisit)
  choose c hcR hcdom y hy hchart hs hb hw hrad hspeed using
    (fun n : ℕ => H n (1 / ((n : ℝ) + 1)) (by positivity))
  have ht : Tendsto c atTop atTop := tendsto_atTop_mono
    (fun n => (le_max_left (n : ℝ) 0).trans (hcR n).le) tendsto_natCast_atTop_atTop
  have hrt : Tendsto (fun n => normalizedTaubRadiusSq (normalizedMaxCurve x 0 (c n))) atTop (𝓝 0) :=
    squeeze_zero (fun n => taubRadiusSq_nonneg _ _ _) (fun n => (hrad n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hheight (n : ℕ) : normalizedMaxCurve x 0 (c n) 2 = h := by
    rw [← hchart n]
    rfl
  have hbt : Tendsto (fun n => normalizedMaxCurve x 0 (c n) 3) atTop (𝓝 0) := by
    have HT := ((hprod 0 1 (by decide)).comp ht).div_const h
    change Tendsto (fun n => (normalizedMaxCurve x 0 (c n) 2 * normalizedMaxCurve x 0 (c n) 3) / h)
      atTop (𝓝 (0 / h)) at HT
    simpa only [hheight, mul_div_cancel_left₀ _ hh.ne', zero_div] using HT
  have hwt : Tendsto (fun n => normalizedMaxCurve x 0 (c n) 4) atTop (𝓝 0) := by
    have HT := ((hprod 0 2 (by decide)).comp ht).div_const h
    change Tendsto (fun n => (normalizedMaxCurve x 0 (c n) 2 * normalizedMaxCurve x 0 (c n) 4) / h)
      atTop (𝓝 (0 / h)) at HT
    simpa only [hheight, mul_div_cancel_left₀ _ hh.ne', zero_div] using HT
  exact ⟨c, ht, tendsto_mainWall_boundary (fun n => ⟨y n, hchart n⟩) hrt hbt hwt,
    fun n => ⟨(le_max_right (n : ℝ) 0).trans_lt (hcR n), hcdom n,
      y n, hy n, hchart n, hs n, hb n, hw n⟩⟩

def primaryAxisBoundary (i : Fin 3) (h : ℝ) : NormalizedState :=
  (primaryAxisFrame i).map.symm (mainWallBoundary h)

theorem primaryAxisBoundary_coordinates (i : Fin 3) (h : ℝ) :
    normalizedShears (primaryAxisBoundary i h) =
      (fun j => Real.sqrt (1 - h ^ 2) * normalizedShears (taubPoint i) j) ∧
    normalizedWalls (primaryAxisBoundary i h) = (fun j => if j = i then h else 0) := by
  have hmap : (primaryAxisFrame i).map (primaryAxisBoundary i h) = mainWallBoundary h :=
    (primaryAxisFrame i).map.apply_symm_apply _
  constructor
  · ext j
    have H := congrArg (fun z => normalizedShears z ((Equiv.swap 0 i) j)) hmap
    simp only [primaryAxisFrame, axisPermutation_shears, Equiv.swap_apply_self] at H
    rw [H, normalizedShears_taubPoint]
    fin_cases i <;> fin_cases j <;>
      simp [mainWallBoundary, normalizedShears, Equiv.swap_apply_def] <;> ring
  · ext j
    have H := congrArg (fun z => normalizedWalls z ((Equiv.swap 0 i) j)) hmap
    simp only [primaryAxisFrame, axisPermutation_walls, Equiv.swap_apply_self] at H
    rw [H]
    fin_cases i <;> fin_cases j <;>
      simp [mainWallBoundary, normalizedWalls, Equiv.swap_apply_def]

/-- The geometric crossing limit is attached to the specified physical axis, with original times unchanged. -/
theorem exists_primaryAxis_section_limit (i : Fin 3) {x : NormalizedState} {h d : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hr : 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x))
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hprod : ∀ j k : Fin 3, j ≠ k → Tendsto
      (fun t => wallValue j (normalizedMaxCurve x 0 t) * wallValue k (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    (hvisit : taubPoint i ∈ normalizedOmegaLimit x) :
    ∃ c : ℕ → ℝ, Tendsto c atTop atTop ∧
      Tendsto (fun n => normalizedMaxCurve x 0 (c n)) atTop (𝓝 (primaryAxisBoundary i h)) ∧
      ∀ n, 0 < c n ∧ c n ∈ normalizedMaxDomain x 0 ∧
        ∃ y ∈ mainWallChartDomain h, axisWallChart (primaryAxisFrame i) h y = normalizedMaxCurve x 0 (c n) ∧
          |y 0| < d ∧ Real.exp (-y 1) < d ∧ Real.exp (-y 2) < d := by
  have hv := normalizedOmegaLimit_symmetry (primaryAxisFrame i) hc hvisit
  rw [primaryAxisFrame_taubPoint] at hv
  obtain ⟨c, ht, hz, Hc⟩ := exists_taub_section_limit
    (((primaryAxisFrame i).constraint x).trans hc) (((primaryAxisFrame i).positive x).mpr hp)
    hr hh hhmax hd hdh (wallProductDecay_axisPermutation hp hc hprod _) hv
  have hdom (n : ℕ) : c n ∈ normalizedMaxDomain x 0 := by
    simpa only [(primaryAxisFrame i).maxDomain] using (Hc n).2.1
  have horbit (n : ℕ) : (primaryAxisFrame i).map.symm
      (normalizedMaxCurve ((primaryAxisFrame i).map x) 0 (c n)) = normalizedMaxCurve x 0 (c n) := by
    rw [(primaryAxisFrame i).maxCurve (hdom n), ContinuousLinearEquiv.symm_apply_apply]
  have hlim := (primaryAxisFrame i).map.symm.continuous.continuousAt.tendsto.comp hz
  refine ⟨c, ht, ?_, ?_⟩
  · simpa only [Function.comp_def, horbit, primaryAxisBoundary] using hlim
  · intro n
    obtain ⟨hn, _, y, hy, hchart, hs, hb, hw⟩ := Hc n
    refine ⟨hn, hdom n, y, hy, ?_, hs, hb, hw⟩
    change (primaryAxisFrame i).map.symm (mainWallChart h y) = _
    rw [hchart, horbit n]

theorem primaryAxisBoundary_mem_omegaLimit (i : Fin 3) {x : NormalizedState} {h d : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hr : 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x))
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hprod : ∀ j k : Fin 3, j ≠ k → Tendsto
      (fun t => wallValue j (normalizedMaxCurve x 0 t) * wallValue k (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    (hvisit : taubPoint i ∈ normalizedOmegaLimit x) :
    primaryAxisBoundary i h ∈ normalizedOmegaLimit x := by
  obtain ⟨c, ht, hz, _⟩ := exists_primaryAxis_section_limit i hc hp hr hh hhmax hd hdh hprod hvisit
  exact mem_normalizedOmegaLimit_of_sequence ht hz

end BianchiIX
