import BianchiIX.Algebra.SingleWallBounds
import BianchiIX.Dynamics.ConstrainedComplete

noncomputable section

namespace BianchiIX

open Set

/-- The squared bounds corresponding to `2 * sqrt (N_i * N_j) <= Delta`. -/
def normalizedWallProductsBound (Δ : ℝ) (x : NormalizedState) : Prop :=
  4 * x 2 * x 3 ≤ Δ ^ 2 ∧ 4 * x 3 * x 4 ≤ Δ ^ 2 ∧ 4 * x 4 * x 2 ≤ Δ ^ 2

theorem normalized_singleWall_estimates {x : NormalizedState} {Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hprod : normalizedWallProductsBound Δ x) (hν : 0 < ν) (hνmax : ν ≤ 1 / 4)
    (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8) (hn : ν ≤ x 2) :
    x 3 + x 4 ≤ Δ ^ 2 / (2 * x 2) ∧ x 3 + x 4 ≤ ν / 128 ∧
      |x 0| < 17 / 16 ∧ normalizedField x 0 ≤ -(x 2 ^ 2) / 2 ∧
      normalizedField x 0 ≤ -(ν ^ 2) / 2 := by
  obtain ⟨hweak, hweak'⟩ := weak_wall_sum_of_products hν hn hp.2.1.le hp.2.2.le hΔ hprod.1 hprod.2.2
  have hΔmax : Δ ≤ 1 / 4 := by linarith only [hΔ.2, hνmax]
  have habs := (constraint_small_wall_products hc hprod.1 hprod.2.1 hprod.2.2 ⟨hΔ.1, hΔmax⟩).2.2
  have hfield : normalizedField x 0 ≤ -(x 2 ^ 2) / 2 :=
    shearPlus_single_wall_descent habs.le hp.1.le hp.2.1.le hp.2.2.le
      (by linarith only [hweak', hn, hν])
  exact ⟨hweak, hweak', habs, hfield, by nlinarith only [hfield, hn, hν]⟩

/-- A single-wall interval has uniformly bounded length in the original normalized time. -/
theorem normalized_singleWall_residence {x : NormalizedState} {t₀ s t Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hν : 0 < ν) (hνmax : ν ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8)
    (hs : t₀ ≤ s) (hst : s ≤ t)
    (hprod : ∀ u ∈ Icc s t, normalizedWallProductsBound Δ (normalizedMaxCurve x t₀ u))
    (hn : ∀ u ∈ Icc s t, ν ≤ normalizedMaxCurve x t₀ u 2) : t - s < 5 / ν ^ 2 := by
  let p := fun u => normalizedMaxCurve x t₀ u 0
  have H (u : ℝ) (hu : u ∈ Icc s t) :
      |p u| < 17 / 16 ∧ normalizedField (normalizedMaxCurve x t₀ u) 0 ≤ -(ν ^ 2) / 2 := by
    have htime := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
    have hpos := normalized_positive_walls_invariant
      (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
      (fun u hu => hasDerivAt_normalizedMaxCurve hu)
      (initial_mem_normalizedMaxDomain x t₀) htime
      (by simpa only [normalizedMaxCurve_initial] using hp)
    have he := normalized_singleWall_estimates
      (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).2.1 hpos (hprod u hu) hν hνmax hΔ (hn u hu)
    exact ⟨he.2.2.1, he.2.2.2.2⟩
  have hd (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt p (normalizedField (normalizedMaxCurve x t₀ u) 0) u :=
    hasDerivAt_pi.mp (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).1 0
  have hdiff := (convex_Icc s t).image_sub_le_mul_sub_of_deriv_le (HasDerivAt.continuousOn hd)
    (fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by rw [(hd u (interior_subset hu)).deriv]; exact (H u (interior_subset hu)).2)
    s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  have hps := (abs_lt.mp (H s ⟨le_rfl, hst⟩).1).2
  have hpt := (abs_lt.mp (H t ⟨hst, le_rfl⟩).1).1
  apply (lt_div_iff₀ (sq_pos_of_pos hν)).mpr
  nlinarith only [hdiff, hps, hpt]

/-- Every forward single-wall stay ends within a fixed finite time. -/
theorem exists_normalized_singleWall_exit {x : NormalizedState} {t₀ s Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hν : 0 < ν) (hνmax : ν ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8) (hs : t₀ ≤ s)
    (hprod : ∀ u ∈ Icc s (s + 5 / ν ^ 2),
      normalizedWallProductsBound Δ (normalizedMaxCurve x t₀ u)) :
    ∃ u ∈ Icc s (s + 5 / ν ^ 2), normalizedMaxCurve x t₀ u 2 < ν := by
  by_contra! H
  have hh := normalized_singleWall_residence hc hp hν hνmax hΔ hs
    (by
      have hlength : 0 < 5 / ν ^ 2 := by positivity
      linarith only [hlength]) hprod H
  linarith only [hh]

end BianchiIX
