import BianchiIX.Dynamics.SingleWallExit
import BianchiIX.Dynamics.AxisPermutations
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace BianchiIX

open Set

theorem axisFrame_wallValue (a : Fin 6) (x : NormalizedState) (i : Fin 3) :
    wallValue i ((axisFrame a).map x) = wallValue (axisOrder a i) x := by
  have heq (y : NormalizedState) (j : Fin 3) : normalizedWalls y j = wallValue j y := by
    fin_cases j <;> rfl
  simpa only [heq] using congrFun (axisFrame_walls a x) i

theorem normalizedWallProductsBound.axisFrame {x : NormalizedState} {Δ : ℝ}
    (H : normalizedWallProductsBound Δ x) (a : Fin 6) :
    normalizedWallProductsBound Δ ((axisFrame a).map x) := by
  fin_cases a <;>
    simpa [normalizedWallProductsBound, axisFrame_apply, axisCycle, axisSwap,
      mul_comm, mul_left_comm, mul_assoc, and_assoc, and_comm, and_left_comm] using H

/-- A dominant first wall leads into the strict small-wall region within the same finite window. -/
theorem exists_smallWall_entry_from_first_wall {x : NormalizedState} {Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hν : 0 < ν) (hνmax : ν ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8)
    (hn : ν ≤ x 2)
    (hprod : ∀ u ∈ Icc 0 (5 / ν ^ 2), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) :
    ∃ u ∈ Icc 0 (5 / ν ^ 2), ∀ i : Fin 3, wallValue i (normalizedMaxCurve x 0 u) < ν := by
  obtain ⟨T, hT, hbelow⟩ := exists_normalized_singleWall_exit hc hp hν hνmax hΔ (le_refl 0)
    (by simpa only [zero_add] using hprod)
  simp only [zero_add] at hT
  let n := fun u => normalizedMaxCurve x 0 u 2
  have hpositive : 0 < n T := by
    exact normalized_wall_pos (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
      (fun u hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.1) 0
      (by simpa only [normalizedMaxCurve_initial] using! hp.1)
  let r := (ν + n T) / 2
  have hr : ν / 2 ≤ r ∧ r < ν := by dsimp [r, n] at *; constructor <;> linarith only [hpositive, hbelow]
  have hstart : r ≤ n 0 := by simpa only [n, normalizedMaxCurve_initial] using hr.2.le.trans hn
  have hlast : n T ≤ r := by dsimp [r]; linarith only [hbelow]
  have hcont : ContinuousOn n (Icc 0 T) := fun u hu =>
    (hasDerivAt_pi.mp (normalizedMaxCurve_forward_of_constraint hc hu.1).1 2).continuousAt.continuousWithinAt
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc' hT.1 hcont ⟨hlast, hstart⟩
  have htime := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hu.1
  have hpos := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun v hv => hasDerivAt_normalizedMaxCurve hv) (initial_mem_normalizedMaxDomain x 0) htime
    (by simpa only [normalizedMaxCurve_initial] using hp)
  have hpairs := hprod u ⟨hu.1, hu.2.trans hT.2⟩
  let y := normalizedMaxCurve x 0 u
  have hsum : 2 * y 2 * (y 3 + y 4) ≤ Δ ^ 2 := by
    nlinarith only [hpairs.1, hpairs.2.2]
  have hheight : ν / 2 ≤ y 2 := by change ν / 2 ≤ n u; rw [heq]; exact hr.1
  have hcompare := mul_le_mul_of_nonneg_right hheight (add_nonneg hpos.2.1.le hpos.2.2.le)
  have hΔsq : Δ ^ 2 ≤ ν ^ 2 / 64 := by nlinarith only [hΔ.1, hΔ.2, hν]
  have hweak : y 3 + y 4 < ν := by nlinarith only [hsum, hcompare, hΔsq, hν]
  refine ⟨u, ⟨hu.1, hu.2.trans hT.2⟩, ?_⟩
  intro i
  fin_cases i
  · change n u < ν
    rw [heq]
    exact hr.2
  · change y 3 < ν
    linarith only [hweak, hpos.2.2]
  · change y 4 < ν
    linarith only [hweak, hpos.2.1]

/-- Small pairwise products force every positive orbit into the strict small-wall region in finite time. -/
theorem exists_normalized_smallWall_entry {x : NormalizedState} {Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hν : 0 < ν) (hνmax : ν ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8)
    (hprod : ∀ u ∈ Icc 0 (5 / ν ^ 2), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) :
    ∃ u ∈ Icc 0 (5 / ν ^ 2), ∀ i : Fin 3, wallValue i (normalizedMaxCurve x 0 u) < ν := by
  by_cases hsmall : ∀ i : Fin 3, wallValue i x < ν
  · refine ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩
    simpa only [normalizedMaxCurve_initial] using hsmall
  push Not at hsmall
  obtain ⟨i, hi⟩ := hsmall
  have hframe : ∃ a : Fin 6, axisOrder a 0 = i := by
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨a, ha⟩ := hframe
  let A := axisFrame a
  have hcA : stateConstraint (A.map x) = 1 := (A.constraint x).trans hc
  have hpA : positiveWalls (A.map x) := (A.positive x).mpr hp
  have hprodA (u : ℝ) (hu : u ∈ Icc 0 (5 / ν ^ 2)) :
      normalizedWallProductsBound Δ (normalizedMaxCurve (A.map x) 0 u) := by
    rw [A.maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hu.1)]
    exact (hprod u hu).axisFrame a
  have hnA : ν ≤ A.map x 2 := by
    change ν ≤ wallValue 0 ((axisFrame a).map x)
    rw [axisFrame_wallValue, ha]
    exact hi
  obtain ⟨u, hu, hall⟩ := exists_smallWall_entry_from_first_wall hcA hpA hν hνmax hΔ hnA hprodA
  refine ⟨u, hu, ?_⟩
  intro j
  obtain ⟨k, hk⟩ := (axisOrder_bijective a).surjective j
  have HH := hall k
  rw [A.maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hu.1)] at HH
  simpa only [A, axisFrame_wallValue, hk] using HH

end BianchiIX
