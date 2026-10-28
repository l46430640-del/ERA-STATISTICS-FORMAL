import BianchiIX.Dynamics.TaubArcLimit
import BianchiIX.Analysis.ClusterExtrema

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def normalizedMaxWall (x : NormalizedState) : ℝ :=
  max (wallValue 0 x) (max (wallValue 1 x) (wallValue 2 x))

theorem normalizedMaxWall_le_iff {x : NormalizedState} {b : ℝ} :
    normalizedMaxWall x ≤ b ↔ ∀ i : Fin 3, wallValue i x ≤ b := by
  simp only [normalizedMaxWall, max_le_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> assumption
  · exact fun h => ⟨h 0, h 1, h 2⟩

theorem wallValue_primaryAxisArc_zero (i j : Fin 3) :
    wallValue j (primaryAxisArc i 0) = if j = i then 1 else 0 := by
  have H := congrFun (primaryAxisArc_coordinates i 0).2 j
  fin_cases j <;> simpa [wallValue, normalizedWalls] using H

theorem shearSq_primaryAxisArc_zero (i : Fin 3) :
    shearSq (primaryAxisArc i 0 0) (primaryAxisArc i 0 1) = 0 := by
  have H0 := congrFun (primaryAxisArc_coordinates i 0).1 0
  have H1 := congrFun (primaryAxisArc_coordinates i 0).1 1
  simp only [normalizedShears, Matrix.cons_val_zero, zero_mul] at H0
  have hp : primaryAxisArc i 0 0 = 0 := by linarith only [H0]
  have hs : primaryAxisArc i 0 1 = 0 := by
    simp only [normalizedShears, Matrix.cons_val_one, Matrix.cons_val_zero, zero_mul, hp,
      zero_sub, neg_eq_zero] at H1
    exact (mul_eq_zero.mp H1).resolve_left (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
  simp [shearSq, hp, hs]

theorem normalizedMaxWall_primaryAxisArc_zero (i : Fin 3) :
    normalizedMaxWall (primaryAxisArc i 0) = 1 := by
  simp only [normalizedMaxWall, wallValue_primaryAxisArc_zero]
  fin_cases i <;> norm_num [Fin.ext_iff]

/-- The constraint controls every wall by the same expression, tending to one when pair products vanish. -/
theorem wallValue_le_constraint_sqrt {x : NormalizedState} (hc : stateConstraint x = 1)
    (i : Fin 3) : wallValue i x ≤
      Real.sqrt (1 + 2 * (wallValue 0 x * wallValue 1 x +
        wallValue 1 x * wallValue 2 x + wallValue 2 x * wallValue 0 x)) := by
  have he : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2 =
      1 + 2 * (x 2 * x 3 + x 3 * x 4 + x 4 * x 2) := by
    dsimp [stateConstraint, constraint, shearSq, curvature] at hc
    linarith only [hc]
  have hn : 0 ≤ 1 + 2 * (x 2 * x 3 + x 3 * x 4 + x 4 * x 2) := by
    nlinarith only [he, sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 3), sq_nonneg (x 4)]
  have hs := Real.sq_sqrt hn
  have hpos := Real.sqrt_nonneg (1 + 2 * (x 2 * x 3 + x 3 * x 4 + x 4 * x 2))
  fin_cases i <;> dsimp [wallValue] <;>
    nlinarith only [he, hs, hpos, sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 3), sq_nonneg (x 4)]

theorem tendsto_constraint_wall_bound {x : NormalizedState}
    (hprod : ∀ j k : Fin 3, j ≠ k → Tendsto
      (fun t => wallValue j (normalizedMaxCurve x 0 t) * wallValue k (normalizedMaxCurve x 0 t)) atTop (𝓝 0)) :
    Tendsto (fun t => Real.sqrt (1 + 2 *
      (wallValue 0 (normalizedMaxCurve x 0 t) * wallValue 1 (normalizedMaxCurve x 0 t) +
        wallValue 1 (normalizedMaxCurve x 0 t) * wallValue 2 (normalizedMaxCurve x 0 t) +
        wallValue 2 (normalizedMaxCurve x 0 t) * wallValue 0 (normalizedMaxCurve x 0 t)))) atTop (𝓝 1) := by
  have H := (((hprod 0 1 (by decide)).add (hprod 1 2 (by decide))).add (hprod 2 0 (by decide)))
  simpa only [add_zero, mul_zero, Real.sqrt_one] using ((H.const_mul 2).const_add 1).sqrt

theorem taub_arc_center_extrema (i : Fin 3) {x : NormalizedState}
    (hc : stateConstraint x = 1)
    (hprod : ∀ j k : Fin 3, j ≠ k → Tendsto
      (fun t => wallValue j (normalizedMaxCurve x 0 t) * wallValue k (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    (hz : primaryAxisArc i 0 ∈ normalizedOmegaLimit x) :
    limsup (fun t => wallValue i (normalizedMaxCurve x 0 t)) atTop = 1 ∧
      limsup (fun t => normalizedMaxWall (normalizedMaxCurve x 0 t)) atTop = 1 ∧
      liminf (fun t => shearSq (normalizedMaxCurve x 0 t 0) (normalizedMaxCurve x 0 t 1)) atTop = 0 := by
  change MapClusterPt (primaryAxisArc i 0) atTop (normalizedMaxCurve x 0) at hz
  have hw : MapClusterPt 1 atTop (fun t => wallValue i (normalizedMaxCurve x 0 t)) := by
    have H := hz.continuousAt_comp (show ContinuousAt (wallValue i) (primaryAxisArc i 0) by
      exact (continuous_apply (i.addNat 2)).continuousAt)
    simpa [wallValue_primaryAxisArc_zero, Function.comp_def] using H
  have hm : MapClusterPt 1 atTop (fun t => normalizedMaxWall (normalizedMaxCurve x 0 t)) := by
    have H := hz.continuousAt_comp (show ContinuousAt normalizedMaxWall (primaryAxisArc i 0) by
      unfold normalizedMaxWall wallValue
      fun_prop)
    simpa only [normalizedMaxWall_primaryAxisArc_zero, Function.comp_def] using H
  have hs : MapClusterPt 0 atTop
      (fun t => shearSq (normalizedMaxCurve x 0 t 0) (normalizedMaxCurve x 0 t 1)) := by
    have H := hz.continuousAt_comp (show ContinuousAt (fun z : NormalizedState => shearSq (z 0) (z 1))
        (primaryAxisArc i 0) by unfold shearSq; fun_prop)
    simpa only [shearSq_primaryAxisArc_zero, Function.comp_def] using H
  have Hbound := tendsto_constraint_wall_bound hprod
  have he : ∀ᶠ t : ℝ in atTop, ∀ j : Fin 3, wallValue j (normalizedMaxCurve x 0 t) ≤
      Real.sqrt (1 + 2 * (wallValue 0 (normalizedMaxCurve x 0 t) * wallValue 1 (normalizedMaxCurve x 0 t) +
        wallValue 1 (normalizedMaxCurve x 0 t) * wallValue 2 (normalizedMaxCurve x 0 t) +
        wallValue 2 (normalizedMaxCurve x 0 t) * wallValue 0 (normalizedMaxCurve x 0 t))) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact wallValue_le_constraint_sqrt ((normalizedMaxCurve_constraint
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht)).trans hc)
  exact ⟨limsup_eq_of_cluster_upper hw Hbound (he.mono fun _ h => h i),
    limsup_eq_of_cluster_upper hm Hbound (he.mono fun _ h => normalizedMaxWall_le_iff.mpr h),
    liminf_eq_of_cluster_lower hs (Eventually.of_forall fun t =>
      add_nonneg (sq_nonneg _) (sq_nonneg _))⟩

theorem taubPoint_extrema (i : Fin 3) {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hr : 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x))
    (hprod : ∀ j k : Fin 3, j ≠ k → Tendsto
      (fun t => wallValue j (normalizedMaxCurve x 0 t) * wallValue k (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    (hz : taubPoint i ∈ normalizedOmegaLimit x) :
    limsup (fun t => wallValue i (normalizedMaxCurve x 0 t)) atTop = 1 ∧
      limsup (fun t => normalizedMaxWall (normalizedMaxCurve x 0 t)) atTop = 1 ∧
      liminf (fun t => shearSq (normalizedMaxCurve x 0 t 0) (normalizedMaxCurve x 0 t 1)) atTop = 0 :=
  taub_arc_center_extrema i hc hprod (primaryAxisArc_closed_mem_omegaLimit_of_taub i hc hp hr hprod hz
    0 (by constructor <;> norm_num))

end BianchiIX
