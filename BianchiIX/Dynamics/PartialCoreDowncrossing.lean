import BianchiIX.Dynamics.ActiveWallDowncrossing
import BianchiIX.Dynamics.PartialCoreFirstReturn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The outgoing event remains the first negative crossing on an ambient neighborhood of an incoming-boundary entry. -/
theorem exists_normalized_partialCore_downcrossing_two {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → (1 < β s 2 ∨ (β s 2 = 1 ∧ 1 ≤ β s 0)) →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, IsLeast {u | s < u ∧ β u 2 = 1} t ∧
      (∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u)) ∧
      ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
        ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y))) x ∧
        HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x t₀ t) x ∧
        HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y)))
          ((fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)).comp
            (normalizedEventDifferential projectiveActiveWall x t₀ t)) x ∧
        (∀ᶠ y in 𝓝 x,
          IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain y t₀ ∧
            projectiveActiveWall (normalizedMaxCurve y t₀ u) = 1 ∧
            normalizedEventRate projectiveActiveWall y t₀ u < 0} (τ y) ∧
          (∀ u ∈ Icc s (τ y), u ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ u 0)) := by
  intro β hR hV hU hP
  obtain ⟨t, hst, hfirst, _, _, hder, _, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk hs hA hR hV hU hP
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have hcore (u : ℝ) (hu : u ∈ Icc s t) :
      0 < 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u) :=
    ⟨lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H u hu).1, (H u hu).2.1⟩
  have hreg (u : ℝ) (hu : u ∈ Icc s t) :
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    ⟨normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1), (hcore u hu).1⟩
  have HD (u : ℝ) (hu : u ∈ Icc s t) : HasDerivAt (fun v => β v 2)
      (normalizedEventRate projectiveActiveWall x t₀ u) u :=
    ((contDiffAt_projectiveActiveWall 1 (ne_of_gt (hreg u hu).2)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_normalizedMaxCurve (hreg u hu).1)
  have hbefore (u : ℝ) (hu : u ∈ Ico s t) :
      projectiveActiveWall (normalizedMaxCurve x t₀ u) ≠ 1 ∨
        0 < normalizedEventRate projectiveActiveWall x t₀ u := by
    rcases eq_or_lt_of_le hu.1 with heq | hsu
    · subst u
      rcases hV with hv | ⟨hv, hm⟩
      · exact Or.inl (ne_of_gt hv)
      · right
        have hsm : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
        have Hflow := normalizedMaxCurve_forward_of_constraint hc hs
        have Hup := scaled_core_entry_upward hk hA
          (hasDerivAt_toProjectiveState_normalized Hflow.1 hA.ne' Hflow.2.1) hv hm
          (coreRegion_radius_bounds hk (hcore s hsm).2).1 hU
          (coreRegion_wall_bounds (hcore s hsm).2).2
        rw [(HD s hsm).deriv] at Hup
        exact (by positivity : 0 < (1 + normalizedMaxCurve x t₀ s 0) * k / 2).trans_le Hup.2.1
    · left
      intro hh
      exact (not_le_of_gt hu.2) (hfirst.2 ⟨hsu, hh⟩)
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  rw [(HD t htm).deriv] at hder
  have hrate : normalizedEventRate projectiveActiveWall x t₀ t < 0 := hder.trans_lt (by
    have Hpos := (hcore t htm).1
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos Hpos) hkpos) (by norm_num))
  exact ⟨t, hst, hfirst, hcore,
    exists_activeWall_first_downcrossing_two hst hreg hbefore hrate hfirst.1.2⟩

end BianchiIX
