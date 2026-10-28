import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Strict expansion on a finite-measure invariant failure set, Section 7.1. -/

open MeasureTheory Set
open scoped ENNReal

namespace BianchiIX

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- No uniform lower bound above one is required for the Jacobian. -/
theorem null_of_strict_expansion
    {A : Set X} {R : X → X} {j : X → ℝ≥0∞}
    (hfinite : μ A ≠ ∞)
    (hj : AEMeasurable j (μ.restrict A))
    (hexpand : ∀ᵐ x ∂μ.restrict A, 1 < j x)
    (hchange : μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    (hinvariant : R '' A ⊆ A) : μ A = 0 := by
  by_contra hpos
  have hμ : μ.restrict A ≠ 0 := by
    simpa using hpos
  have hlt := lintegral_strict_mono (f := fun _ : X => (1 : ℝ≥0∞))
    hμ hj (by simpa using hfinite) hexpand
  have : μ A < μ (R '' A) := by simpa [hchange] using hlt
  exact (not_lt_of_ge (measure_mono hinvariant)) this

/-- Iterates outside the return domain are excluded, even if a total extension is used. -/
def permanentFailure (R : X → X) (D E : Set X) : Set X :=
  {x | ∀ n : ℕ, R^[n] x ∈ D ∩ E}

theorem permanentFailure_measurable
    {R : X → X} {D E : Set X}
    (hR : Measurable R) (hD : MeasurableSet D) (hE : MeasurableSet E) :
    MeasurableSet (permanentFailure R D E) := by
  simp only [permanentFailure, ofPred_forall]
  exact MeasurableSet.iInter fun n => (hD.inter hE).preimage (hR.iterate n)

omit [MeasurableSpace X] in
theorem permanentFailure_subset {R : X → X} {D E : Set X} :
    permanentFailure R D E ⊆ D ∩ E := by
  intro x hx
  exact hx 0

omit [MeasurableSpace X] in
theorem permanentFailure_invariant {R : X → X} {D E : Set X} :
    R '' permanentFailure R D E ⊆ permanentFailure R D E := by
  rintro _ ⟨x, hx, rfl⟩ n
  simpa only [Function.iterate_succ_apply] using hx (n + 1)

/-- The change-of-variables hypothesis is needed only for measurable subsets of D. -/
theorem permanentFailure_null
    {R : X → X} {D E : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hfinite : μ E ≠ ∞) (hj : Measurable j)
    (hexpand : ∀ x ∈ D, 1 < j x)
    (hchange : ∀ B, MeasurableSet B → B ⊆ D →
      μ (R '' B) = ∫⁻ x in B, j x ∂μ) :
    μ (permanentFailure R D E) = 0 := by
  have hA := permanentFailure_measurable hR hD hE
  have hAD : permanentFailure R D E ⊆ D :=
    fun _ hx => (permanentFailure_subset hx).1
  have hAE : permanentFailure R D E ⊆ E :=
    fun _ hx => (permanentFailure_subset hx).2
  apply null_of_strict_expansion
    (ne_top_of_le_ne_top hfinite (measure_mono hAE)) hj.aemeasurable
    _ (hchange _ hA hAD) permanentFailure_invariant
  exact (ae_restrict_mem hA).mono fun x hx => hexpand x (hAD hx)

theorem ae_eventually_leaves_failure
    {R : X → X} {D E : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hfinite : μ E ≠ ∞) (hj : Measurable j)
    (hexpand : ∀ x ∈ D, 1 < j x)
    (hchange : ∀ B, MeasurableSet B → B ⊆ D →
      μ (R '' B) = ∫⁻ x in B, j x ∂μ) :
    ∀ᵐ x ∂μ, (∀ n : ℕ, R^[n] x ∈ D) → ∃ n : ℕ, R^[n] x ∉ E := by
  have hnull := permanentFailure_null hR hD hE hfinite hj hexpand hchange
  have houtside : ∀ᵐ x ∂μ, x ∉ permanentFailure R D E := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hnull
  filter_upwards [houtside] with x hx hreturns
  by_contra h
  push Not at h
  exact hx (fun n => ⟨hreturns n, h n⟩)

end BianchiIX
