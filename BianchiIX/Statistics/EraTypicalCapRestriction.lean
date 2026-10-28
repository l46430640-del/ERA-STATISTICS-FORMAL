import BianchiIX.Statistics.EraCapMonotonicity
import BianchiIX.Statistics.EraRadialStatistics

noncomputable section

namespace BianchiIX

open Set

/-- A typical history is unchanged under a new cap containing its initial budget, provided that budget is at most one. -/
theorem EraSurvivor.typicalDomain_restrict_cap {η σ B₁ B₂ : ℝ} {J : ℕ}
    {p : ℝ × CoreAngleState} (hp : p ∈ typicalDomain η J σ B₁)
    (hone : p.1 ≤ 1) (hB : p.1 ≤ B₂) : p ∈ typicalDomain η J σ B₂ := by
  rcases hp with ⟨q, hq, rfl⟩
  let r : eraSurvivorDomain η J σ B₂ := ⟨q.val, eraSurvivorDomain_restrict_cap q.property hone hB⟩
  refine ⟨r, ?_, rfl⟩
  change gaussCode (digits r) ∈ gaussCylinderTypicalSet
  rw [← digits_eq_of_val q r rfl]
  exact hq

/-- Once the actual budget fits the target cap, failure there implies failure under any comparison cap. -/
theorem eraRadialFailure_subset_of_budget {η σ B B₁ B₂ a b : ℝ} {J : ℕ}
    (hone : B ≤ 1) (hB : B ≤ B₂) (Y : ℝ → CoreAngleState) :
    eraRadialFailure η J σ B B₂ a b Y ⊆ eraRadialFailure η J σ B B₁ a b Y := by
  intro r hr
  exact ⟨hr.1, fun hg => hr.2 (EraSurvivor.typicalDomain_restrict_cap hg hone hB)⟩

end BianchiIX
