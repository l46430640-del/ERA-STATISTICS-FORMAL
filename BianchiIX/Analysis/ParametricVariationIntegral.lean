import BianchiIX.Analysis.IntegralVariation

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A parameter derivative is represented by a time-differentiable integral without assuming a third derivative. -/
theorem exists_parametric_variation_integral
    {J G : E × ℝ → V} {x : E} {a b : ℝ} {w : V}
    (hG : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 G (x, t))
    (hJ : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => J (y, r)) (G (y, t)) t)
    (hinit : ∀ᶠ y in 𝓝 x, J (y, a) = w) (v : E) :
    ∃ Q : ℝ → V, Q a = 0 ∧ ∀ t ∈ Icc a b,
      Q t = fderiv ℝ (fun y => J (y, t)) x v ∧
      HasDerivAt Q (fderiv ℝ G (x, t) (v, 0)) t := by
  let D := fun t => (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  refine ⟨fun t => (∫ r in a..t, D r) v, by simp, ?_⟩
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := fun _ hr => ⟨hr.1, hr.2.trans ht.2⟩
  have HG := fun r hr => hG r (hsub hr)
  have HJ : ∀ᶠ y in 𝓝 x, ∀ r ∈ Icc a t, HasDerivAt (fun s => J (y, s)) (G (y, r)) r :=
    hJ.mono fun _ hy r hr => hy r (hsub hr)
  have HD := hasFDerivAt_of_parametric_ode ht.1 HG HJ hinit
  refine ⟨by rw [HD.fderiv], ?_⟩
  have HI := (hasDerivAt_integral_partial_fderiv ht.1 HG).clm_apply (hasDerivAt_const t v)
  simpa [D] using HI

end BianchiIX
