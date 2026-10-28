import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Tactic.NormNum

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

structure ScalarLocalInverseAt (f : ℝ → ℝ) (a : ℝ) (g : ℝ → ℝ) : Prop where
  apply_base : g (f a) = a
  contDiffAt : ContDiffAt ℝ 1 g (f a)
  hasDerivAt : HasDerivAt g (deriv f a)⁻¹ (f a)
  left_inverse : ∀ᶠ x in 𝓝 a, g (f x) = x
  right_inverse : ∀ᶠ y in 𝓝 (f a), f (g y) = y

theorem exists_scalarLocalInverseAt {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiffAt ℝ 1 f a) (hd : deriv f a ≠ 0) :
    ∃ g, ScalarLocalInverseAt f a g := by
  have hs := hf.hasStrictDerivAt (by norm_num)
  let g := hs.localInverse f (deriv f a) a hd
  refine ⟨g, ⟨(hs.eventually_left_inverse hd).self_of_nhds, ?_,
    (hs.to_localInverse hd).hasDerivAt, hs.eventually_left_inverse hd, hs.eventually_right_inverse hd⟩⟩
  have HE := hs.hasStrictFDerivAt_equiv hd
  exact hf.to_localInverse HE.hasFDerivAt (by norm_num)

theorem ScalarLocalInverseAt.deriv_eq {f g : ℝ → ℝ} {a : ℝ}
    (H : ScalarLocalInverseAt f a g) : deriv g (f a) = (deriv f a)⁻¹ := H.hasDerivAt.deriv

/-- The local branch is unique as a germ, independent of the extension away from its domain. -/
theorem ScalarLocalInverseAt.unique {f g₁ g₂ : ℝ → ℝ} {a : ℝ}
    (H₁ : ScalarLocalInverseAt f a g₁) (H₂ : ScalarLocalInverseAt f a g₂) :
    g₁ =ᶠ[𝓝 (f a)] g₂ := by
  have Hnear : Tendsto g₂ (𝓝 (f a)) (𝓝 a) := by
    simpa only [ContinuousAt, H₂.apply_base] using H₂.contDiffAt.continuousAt
  filter_upwards [H₂.right_inverse, Hnear.eventually H₁.left_inverse] with y hy hxy
  rwa [hy] at hxy

end BianchiIX
