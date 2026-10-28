import BianchiIX.Dynamics.LateTaubCrossing
import BianchiIX.Dynamics.TaubAxes

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem wallProductDecay_axisPermutation {x : NormalizedState}
    (hp : positiveWalls x) (hc : stateConstraint x = 1)
    (hprod : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t))
        atTop (𝓝 0)) (σ : Equiv.Perm (Fin 3)) :
    ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve ((axisPermutation σ).map x) 0 t) *
        wallValue j (normalizedMaxCurve ((axisPermutation σ).map x) 0 t)) atTop (𝓝 0) := by
  intro i j hij
  apply (hprod (σ i) (σ j) (σ.injective.ne hij)).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [axisPermutation_maxCurve σ (normalizedMaxDomain_contains_Ici hp hc 0 ht),
    axisPermutation_wallValue, axisPermutation_wallValue]

/-- Late Taub approaches give late physical crossings of one fixed member of the three-axis family. -/
theorem exists_arbitrarily_late_primaryAxis_crossing {x : NormalizedState} {h d : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hr : ∀ i, 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x))
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hprod : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t))
        atTop (𝓝 0))
    (hvisit : ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R, ∃ i : Fin 3,
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i) < ε) :
    ∃ i : Fin 3, ∀ R : ℝ, ∀ η > (0 : ℝ), ∃ c > max R 0,
      c ∈ normalizedMaxDomain x 0 ∧ ∃ y ∈ mainWallChartDomain h,
        axisWallChart (primaryAxisFrame i) h y = normalizedMaxCurve x 0 c ∧
        |y 0| < d ∧ Real.exp (-y 1) < d ∧ Real.exp (-y 2) < d ∧
        normalizedTaubRadiusSq ((primaryAxisFrame i).map (normalizedMaxCurve x 0 c)) < η := by
  obtain ⟨i, hi⟩ := exists_fixed_late_taub_target hvisit
  have hvisit' : ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R,
      normalizedEuclideanDistance (normalizedMaxCurve ((primaryAxisFrame i).map x) 0 t)
        (taubPoint 0) < ε := by
    intro ε hε R
    obtain ⟨t, ht, hti⟩ := hi ε hε (max R 0)
    refine ⟨t, (le_max_left R 0).trans ht, ?_⟩
    rw [(primaryAxisFrame i).maxCurve
      (normalizedMaxDomain_contains_Ici hp hc 0 ((le_max_right R 0).trans ht)),
      ← primaryAxisFrame_taubPoint i]
    exact (axisPermutation_euclideanDistance _ _ _).trans_lt hti
  have hcross := exists_arbitrarily_late_taub_section_crossing
    ((primaryAxisFrame i).constraint x |>.trans hc) ((primaryAxisFrame i).positive x |>.mpr hp)
    (hr i) hh hhmax hd hdh (wallProductDecay_axisPermutation hp hc hprod _) hvisit'
  refine ⟨i, fun R η hη => ?_⟩
  obtain ⟨c, hcR, hdom, y, hy, hchart, hs, hb, hw, hrad, _⟩ := hcross R η hη
  rw [(primaryAxisFrame i).maxDomain] at hdom
  rw [(primaryAxisFrame i).maxCurve hdom] at hchart hrad
  refine ⟨c, hcR, hdom, y, hy, ?_, hs, hb, hw, hrad⟩
  exact (primaryAxisFrame i).map.injective (by simpa [axisWallChart] using hchart)

end BianchiIX
