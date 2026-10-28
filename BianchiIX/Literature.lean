import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Explicit literature inputs. These propositions are parameters, not project axioms. -/

open Filter MeasureTheory
open scoped Topology

namespace BianchiIX.Literature

/-- The real-valued ergodic probability-space form of Birkhoff's pointwise theorem.
Reference: C. Walkden, Ergodic Theory, Corollary 10.1.2, printed page 89,
https://personalpages.manchester.ac.uk/staff/Charles.Walkden/ergodic-theory/ergodic_theory.pdf
No Gauss-specific conclusion or Einstein-flow estimate is included in this input. -/
def BirkhoffErgodicInput (X : Type*) [MeasurableSpace X] : Prop :=
  ∀ (μ : Measure X), IsProbabilityMeasure μ → ∀ (F : X → X), Ergodic F μ →
    ∀ (f : X → ℝ), Integrable f μ →
      ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ F f n x) atTop (𝓝 (∫ y, f y ∂μ))

end BianchiIX.Literature
