import BianchiIX.Dynamics.DeepTaubCrossing
import BianchiIX.Dynamics.TaubSubspace
import BianchiIX.Dynamics.LateCoreLimit
import BianchiIX.Dynamics.MainWallChart

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Arbitrarily late approach to one Taub point forces arbitrarily late crossings of the same fixed main-wall section. -/
theorem exists_arbitrarily_late_taub_section_crossing {x : NormalizedState} {h d : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x) (hr : 0 < normalizedTaubRadiusSq x)
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hprod : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    (hvisit : ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R,
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint 0) < ε) :
    ∀ R : ℝ, ∀ η > (0 : ℝ), ∃ c > max R 0, c ∈ normalizedMaxDomain x 0 ∧
      ∃ y ∈ mainWallChartDomain h, mainWallChart h y = normalizedMaxCurve x 0 c ∧
        |y 0| < d ∧ Real.exp (-y 1) < d ∧ Real.exp (-y 2) < d ∧
        normalizedTaubRadiusSq (normalizedMaxCurve x 0 c) < η ∧
        normalizedField (normalizedMaxCurve x 0 c) 2 ≤ -5 * h / 4 := by
  intro R η hη
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_normalizedWallProductsBound hprod
    (div_pos hd (by norm_num) : 0 < d / 4))
  let a := max (max R 0) T + 1
  have haR : max R 0 < a := by dsimp [a]; linarith only [le_max_left (max R 0) T]
  have ha0 : 0 ≤ a := (le_max_right R 0).trans haR.le
  have haT : T ≤ a := by dsimp [a]; linarith only [le_max_right (max R 0) T]
  have hRa : 0 < normalizedTaubRadiusSq (normalizedMaxCurve x 0 a) :=
    normalizedTaubRadiusSq_maxCurve_pos (normalizedMaxDomain_contains_Ici hp hc 0 ha0) hr
  let ε := min (min (d / 8) (Real.sqrt (normalizedTaubRadiusSq (normalizedMaxCurve x 0 a)) / 4))
    (Real.sqrt η / 4)
  have hε : 0 < ε := lt_min (lt_min (by positivity) (div_pos (Real.sqrt_pos.mpr hRa) (by norm_num)))
    (div_pos (Real.sqrt_pos.mpr hη) (by norm_num))
  have hεd : ε ≤ d / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hεr : ε ≤ Real.sqrt (normalizedTaubRadiusSq (normalizedMaxCurve x 0 a)) / 4 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hεη : ε ≤ Real.sqrt η / 4 := min_le_right _ _
  have hεr2 := pow_le_pow_left₀ hε.le hεr 2
  have hεη2 := pow_le_pow_left₀ hε.le hεη 2
  have hstart : 4 * ε ^ 2 < normalizedTaubRadiusSq (normalizedMaxCurve x 0 a) := by
    nlinarith only [hεr2, Real.sq_sqrt hRa.le, hRa]
  have hsmall : 2 * ε ^ 2 < η := by nlinarith only [hεη2, Real.sq_sqrt hη.le, hη]
  obtain ⟨b, hb, hbdist⟩ := hvisit ε hε (a + 1)
  have hab : a < b := by linarith only [hb]
  have hphysical (t : ℝ) (ht : t ∈ Icc a b) := normalizedMaxCurve_forward hp hc (ha0.trans ht.1)
  obtain ⟨c, hcint, hnc, hpc, hsc, huc, hwc, hrc, hspeed⟩ := exists_deep_taub_crossing hab
    hh hhmax hd hdh hε (by linarith only [hεd, hd])
    (fun t ht => (hphysical t ht).1) (fun t ht => (hphysical t ht).2.2.1)
    (fun t ht => (hphysical t ht).2.1) (fun t ht => hT t (haT.trans ht.1)) hstart hbdist.le
  have hctime : 0 ≤ c := ha0.trans hcint.1.le
  have hcp := normalizedMaxCurve_forward hp hc hctime
  obtain ⟨hy, hchart⟩ := mainWallChart_coordinates hcp.2.1 hcp.2.2.1
    (by linarith only [hpc]) hnc
  refine ⟨c, haR.trans hcint.1, normalizedMaxDomain_contains_Ici hp hc 0 hctime,
    mainWallCoordinates (normalizedMaxCurve x 0 c), hy, hchart, hsc, ?_, ?_, ?_, hspeed⟩
  · simpa [mainWallCoordinates, Real.exp_log hcp.2.1.2.1] using huc
  · simpa [mainWallCoordinates, Real.exp_log hcp.2.1.2.2] using hwc
  · have hdist := pow_le_pow_left₀ (normalizedEuclideanDistance_nonneg _ _) hbdist.le 2
    rw [normalizedTaubDistance_sq] at hdist
    have H := mul_nonneg (hphysical b ⟨hab.le, le_rfl⟩).2.1.2.1.le
      (hphysical b ⟨hab.le, le_rfl⟩).2.1.2.2.le
    nlinarith only [hrc, hsmall, hdist, H, sq_nonneg (1 + normalizedMaxCurve x 0 b 0),
      sq_nonneg (normalizedMaxCurve x 0 b 2)]

end BianchiIX
