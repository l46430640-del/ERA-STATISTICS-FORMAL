import BianchiIX.Analysis.ImplicitBranch

noncomputable section

namespace BianchiIX

open scoped Topology

theorem exists_scalar_event_family_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : E × ℝ → ℝ} {x : E} {t a : ℝ}
    (hQ : ContDiffAt ℝ 2 Q (x, t))
    (hd : HasDerivAt (fun u => Q (x, u)) a t) (ha : a ≠ 0) :
    ∃ τ : E → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
      (∀ᶠ y in 𝓝 x, Q (y, τ y) = Q (x, t)) := by
  have htime : (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      a • ContinuousLinearMap.id ℝ ℝ := by
    have H := ((hQ.differentiableAt (by norm_num)).hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right x t)).unique hd.hasFDerivAt
    rw [H]
    ext
    simp [mul_comm]
  have hinv : ((fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ E ℝ)).IsInvertible := by
    rw [htime]
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := a⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext; simp [ha]
    · ext; simp [ha]
  exact ⟨hQ.implicitFunction (by norm_num) hinv,
    hQ.implicitFunction_apply_self (by norm_num) hinv,
    hQ.contDiffAt_implicitFunction (by norm_num) hinv,
    hQ.eventually_apply_implicitFunction (by norm_num) hinv⟩

end BianchiIX
