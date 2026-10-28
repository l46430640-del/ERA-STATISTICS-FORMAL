import BianchiIX.Analysis.CompactVectorIntegral

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ContDiff

universe u

theorem contDiffAt_compact_vector_integral_succ (n : ℕ) :
    ∀ {E V : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E × ℝ → V} {x : E} {a b : ℝ},
      a ≤ b → (∀ t ∈ Icc a b, ContDiffAt ℝ ∞ F (x, t)) →
      ContDiffAt ℝ (n + 1) (fun y => ∫ t in a..b, F (y, t)) x := by
  induction n with
  | zero =>
    intro E V _ _ _ _ F x a b hab hF
    simpa using contDiffAt_compact_vector_integral hab
      (fun t ht => (hF t ht).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞))
  | succ n ih =>
    intro E V _ _ _ _ F x a b hab hF
    let D : E × ℝ → E →L[ℝ] V := fun p =>
      (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hD (t : ℝ) (ht : t ∈ Icc a b) : ContDiffAt ℝ ∞ D (x, t) :=
      ((hF t ht).fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_comp contDiffAt_const
    have hs : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (y, t) := by
      apply isCompact_Icc.eventually_forall_of_forall_eventually
      intro t ht
      exact ((hF t ht).of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by norm_num)
    change ContDiffAt ℝ (((n + 1 : ℕ) + 1 : ℕ)) _ x
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun y => ∫ t in a..b, D (y, t), ⟨_, hs, ?_⟩, ih hab hD⟩
    intro y hy
    exact hasFDerivAt_compact_vector_integral hab hy

/-- Smoothness under integration on a fixed compact interval, including operator-valued integrands. -/
theorem contDiffAt_compact_vector_integral_smooth
    {E V : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E × ℝ → V} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ ∞ F (x, t)) :
    ContDiffAt ℝ ∞ (fun y => ∫ t in a..b, F (y, t)) x :=
  contDiffAt_infty.mpr (fun n => (contDiffAt_compact_vector_integral_succ n hab hF).of_le
    (le_add_of_nonneg_right zero_le_one))

end BianchiIX
