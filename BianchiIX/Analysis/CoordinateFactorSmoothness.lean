import BianchiIX.Analysis.CompactIntegralSmoothness
import BianchiIX.Analysis.CoordinateFactor

noncomputable section

namespace BianchiIX

open Set
open scoped ContDiff

/-- The coordinate integral extends the quotient smoothly across its vanishing coordinate. -/
theorem contDiffAt_coordinateFactor_smooth {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {i : Fin n} {Y : Fin n → ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ f (coordinateSegment i Y s)) :
    ContDiffAt ℝ ∞ (coordinateFactor f i) Y := by
  apply contDiffAt_compact_vector_integral_smooth
    (F := fun p => fderiv ℝ f (coordinateSegment i p.1 p.2) (Pi.single i 1))
    (by norm_num : (0 : ℝ) ≤ 1)
  intro s hs
  have hD := ((hf s hs).fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).comp (Y, s)
    (contDiff_coordinateSegment i ∞).contDiffAt
  exact hD.clm_apply contDiffAt_const

end BianchiIX
