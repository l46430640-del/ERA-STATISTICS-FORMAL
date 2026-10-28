import BianchiIX.Dynamics.SingleWallKasner
import BianchiIX.Dynamics.ReferenceEntrance

noncomputable section

namespace BianchiIX

/-- Order the stable axes so that the single-wall reference radius is at least two. -/
def singleWallFrame (x : NormalizedState) : Fin 6 := if 0 ≤ x 1 then 2 else 4

theorem singleWallFrame_coordinates {x : NormalizedState} (h3 : x 3 = 0) (h4 : x 4 = 0) :
    (axisFrame (singleWallFrame x)).map x =
      ![-(x 0 + Real.sqrt 3 * |x 1|) / 2, (Real.sqrt 3 * x 0 - |x 1|) / 2, 0, x 2, 0] := by
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  by_cases hs : 0 ≤ x 1
  · rw [singleWallFrame, if_pos hs, axisFrame_apply, abs_of_nonneg hs]
    change axisCycle (axisCycle x) = _
    ext i
    fin_cases i <;> simp [axisCycle, h3, h4] <;> ring_nf <;> norm_num [hr] <;> ring
  · rw [singleWallFrame, if_neg hs, axisFrame_apply, abs_of_neg (lt_of_not_ge hs)]
    change axisSwap (axisCycle x) = _
    ext i
    fin_cases i <;> simp [axisCycle, axisSwap, h3, h4] <;> ring

theorem singleWallFrame_chart {x : NormalizedState}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0) (hn : 0 < x 2) :
    0 < 1 + (axisFrame (singleWallFrame x)).map x 0 := by
  let z := (axisFrame (singleWallFrame x)).map x
  have hz := ((axisFrame (singleWallFrame x)).constraint x).trans hc
  have he := singleWallFrame_coordinates h3 h4
  have hsq : z 0 ^ 2 + z 1 ^ 2 + x 2 ^ 2 = 1 := by
    change stateConstraint z = 1 at hz
    have h2 : z 2 = 0 := by rw [show z = _ from he]; rfl
    have h3' : z 3 = x 2 := by rw [show z = _ from he]; rfl
    have h4' : z 4 = 0 := by rw [show z = _ from he]; rfl
    simpa [stateConstraint, constraint, shearSq, curvature, h2, h3', h4'] using hz
  change 0 < 1 + z 0
  nlinarith only [hsq, sq_pos_of_pos hn, sq_nonneg (z 1), sq_nonneg (z 0 + 1)]

/-- The physical Taub distance controls the chart without an asymptotic endpoint. -/
theorem singleWallFrame_taubDistance {x : NormalizedState}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0) :
    normalizedEuclideanDistance ((axisFrame (singleWallFrame x)).map x) (taubPoint 0) ^ 2 =
      2 * (1 + (axisFrame (singleWallFrame x)).map x 0) := by
  let z := (axisFrame (singleWallFrame x)).map x
  have hz := ((axisFrame (singleWallFrame x)).constraint x).trans hc
  rw [singleWallFrame_coordinates h3 h4] at hz
  simp [stateConstraint, constraint, shearSq, curvature] at hz
  rw [normalizedEuclideanDistance_sq, singleWallFrame_coordinates h3 h4]
  simp [Fin.sum_univ_succ, taubPoint]
  nlinarith only [hz]

/-- Exact radius and phase identities after ordering the two stable axes. -/
theorem singleWallFrame_projective_identities {x : NormalizedState}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0) (hn : 0 < x 2) :
    let z := (axisFrame (singleWallFrame x)).map x
    let y := toProjectiveState z
    y 1 = 0 ∧ y 3 = 0 ∧ y 2 = Real.sqrt 3 * x 2 / (1 + z 0) ∧
      (y 0 - 1) * (1 + z 0) = 2 * x 0 - 1 ∧
      ((y 0 - 1) ^ 2 + y 2 ^ 2) * (1 + z 0) = 4 * (1 + z 0) + 4 * Real.sqrt 3 * |x 1| := by
  dsimp only
  let z := (axisFrame (singleWallFrame x)).map x
  let y := toProjectiveState z
  have hA := singleWallFrame_chart hc h3 h4 hn
  change 0 < 1 + z 0 at hA
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : x 0 ^ 2 + |x 1| ^ 2 + x 2 ^ 2 = 1 := by
    simpa [stateConstraint, constraint, shearSq, curvature, h3, h4] using hc
  have he := singleWallFrame_coordinates h3 h4
  have hz0 : z 0 = -(x 0 + Real.sqrt 3 * |x 1|) / 2 := congrFun he 0
  have hz1 : z 1 = (Real.sqrt 3 * x 0 - |x 1|) / 2 := congrFun he 1
  have hz3 : z 3 = x 2 := congrFun he 3
  have hM : y 0 * (1 + z 0) = Real.sqrt 3 * z 1 := div_mul_cancel₀ _ hA.ne'
  have hV : y 2 * (1 + z 0) = Real.sqrt 3 * x 2 := by
    change (Real.sqrt 3 * z 3 / (1 + z 0)) * (1 + z 0) = _
    rw [div_mul_cancel₀ _ hA.ne', hz3]
  have hm : (y 0 - 1) * (1 + z 0) = 2 * x 0 - 1 := by
    calc
      _ = Real.sqrt 3 * z 1 - (1 + z 0) := by nlinarith only [hM]
      _ = _ := by rw [hz0, hz1]; ring_nf; rw [hr]; ring
  refine ⟨?_, ?_, ?_, hm, ?_⟩
  · simp [singleWallFrame_coordinates h3 h4, toProjectiveState, projectiveCoord]
  · simp [singleWallFrame_coordinates h3 h4, toProjectiveState, projectiveCoord]
  · simp [singleWallFrame_coordinates h3 h4, toProjectiveState, projectiveCoord]
  · change ((y 0 - 1) ^ 2 + y 2 ^ 2) * (1 + z 0) = 4 * (1 + z 0) + 4 * Real.sqrt 3 * |x 1|
    apply mul_left_injective₀ hA.ne'
    dsimp only
    calc
      _ = ((y 0 - 1) * (1 + z 0)) ^ 2 + (y 2 * (1 + z 0)) ^ 2 := by ring
      _ = (2 * x 0 - 1) ^ 2 + 3 * x 2 ^ 2 := by rw [hm, hV, mul_pow, hr]
      _ = _ := by
        rw [hz0]
        ring_nf
        rw [hr]
        nlinarith only [hsq]

theorem singleWallFrame_projective_bounds {x : NormalizedState}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hn : 0 < x 2) (hp : 1 / 2 < x 0) :
    let z := (axisFrame (singleWallFrame x)).map x
    let y := toProjectiveState z
    1 < y 0 ∧ 0 < y 2 ∧ 2 ≤ coreRadius (y 0) (y 2) := by
  dsimp only
  let z := (axisFrame (singleWallFrame x)).map x
  let y := toProjectiveState z
  obtain ⟨_, _, hv, hm, hk⟩ := singleWallFrame_projective_identities hc h3 h4 hn
  have hA := singleWallFrame_chart hc h3 h4 hn
  have hm' : 1 < y 0 := by change (y 0 - 1) * (1 + z 0) = _ at hm; nlinarith only [hm, hA, hp]
  have hv' : 0 < y 2 := by change y 2 = _ at hv; rw [hv]; positivity
  have hksq : 4 ≤ (y 0 - 1) ^ 2 + y 2 ^ 2 := by
    change ((y 0 - 1) ^ 2 + y 2 ^ 2) * (1 + z 0) = _ at hk
    have H : 0 ≤ 4 * Real.sqrt 3 * |x 1| := by positivity
    nlinarith only [hk, H, hA]
  refine ⟨hm', hv', ?_⟩
  exact Real.le_sqrt_of_sq_le (by norm_num at hksq ⊢; exact hksq)

end BianchiIX
