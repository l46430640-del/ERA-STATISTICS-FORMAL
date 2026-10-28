import BianchiIX.Dynamics.InteriorWallFirstHit
import BianchiIX.Dynamics.PartialCoreFirstReturn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- At every interior partial-core entry, the actual first exit has an ordinary ambient C2 branch. -/
theorem exists_normalized_partialCore_firstReturn_two {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → 1 < β s 2 →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
      ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y))) x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x t₀ t) x ∧
      HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y)))
        ((fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)).comp
          (normalizedEventDifferential projectiveActiveWall x t₀ t)) x ∧
      (∀ᶠ y in 𝓝 x,
        IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain y t₀ ∧
          projectiveActiveWall (normalizedMaxCurve y t₀ u) = 1} (τ y) ∧
        (∀ u ∈ Icc s (τ y), u ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ u 0) ∧
        normalizedEventRate projectiveActiveWall y t₀ (τ y) < 0) := by
  intro β hR hV hU hP
  obtain ⟨t, hst, hleast, _, _, hder, _, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk hs hA hR (Or.inl hV) hU hP
  have hk0 : 0 < k := by linarith only [hk]
  have hreg (u : ℝ) (hu : u ∈ Icc s t) :
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    ⟨normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1),
      lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H u hu).1⟩
  have havoid (u : ℝ) (hu : u ∈ Ico s t) : projectiveActiveWall (normalizedMaxCurve x t₀ u) ≠ 1 := by
    change β u 2 ≠ 1
    intro heq
    rcases eq_or_lt_of_le hu.1 with he | hlt
    · subst u
      exact (ne_of_gt hV) heq
    · exact (not_le_of_gt hu.2) (hleast.2 ⟨hlt, heq⟩)
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have HD := ((contDiffAt_projectiveActiveWall 1 (ne_of_gt (hreg t htm).2)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve (hreg t htm).1)
  change HasDerivAt (fun u => β u 2) (normalizedEventRate projectiveActiveWall x t₀ t) t at HD
  change deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x t₀ t 0) * k / 2 at hder
  rw [HD.deriv] at hder
  have hrate : normalizedEventRate projectiveActiveWall x t₀ t < 0 := hder.trans_lt
    (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (hreg t htm).2) hk0) (by norm_num))
  exact ⟨t, hst, exists_activeWall_interior_first_hit_two hst hreg havoid hrate hleast.1.2⟩

end BianchiIX
