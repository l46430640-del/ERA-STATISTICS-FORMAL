import BianchiIX.Dynamics.CoreReturnUniform
import BianchiIX.Analysis.DiscreteDissipation

noncomputable section

namespace BianchiIX

/-- The same actual core return pays for each wall and their sum, including zero-wall entries. -/
theorem exists_coreRadiusReturn_power_loss :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ Y : CoreAngleState, 2 ≤ Y 0 →
        (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
        let F := coreReturnState coreRadiusReturnTime Y
        (∀ p : ℝ, 0 < p → ∀ i : Fin 2,
          Y i.succ ^ p / Y 0 ≤ (1 + p * c / 2) / (p * c) * (Y i.succ ^ p - F i.succ ^ p)) ∧
          ∀ p : ℝ, 0 < p →
            (Y 1 + Y 2) ^ p / Y 0 ≤
              (1 + p * c / 2) / (p * c) * ((Y 1 + Y 2) ^ p - (F 1 + F 2) ^ p) := by
  obtain ⟨ε, hε, hεmax, c, hc, hcmax, H⟩ := exists_coreRadiusReturn_uniform_contraction
  refine ⟨ε, hε, hεmax, c, hc, hcmax, ?_⟩
  intro Y hk hu hw F
  have HW := (H Y hk hu hw).2.2.2
  constructor
  · intro p hp i
    have hi : 0 ≤ Y i.succ := by
      fin_cases i
      · exact hu.1
      · exact hw.1
    exact rpow_div_le_core_loss hi (HW i).1 hk hc hp (HW i).2.2
  · intro p hp
    have hsum : F 1 + F 2 ≤ Real.exp (-c / Y 0) * (Y 1 + Y 2) := by
      simpa only [F, mul_add] using! add_le_add (HW 0).2.2 (HW 1).2.2
    exact rpow_div_le_core_loss (add_nonneg hu.1 hw.1) (add_nonneg (HW 0).1 (HW 1).1)
      hk hc hp hsum

/-- Along admissible core entries, any nonincreasing intervening maps preserve the total loss budget. -/
theorem exists_coreRadiusReturn_prefix_loss :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ (n : ℕ) (Y : ℕ → CoreAngleState),
        (∀ j ≤ n, 0 ≤ Y j 1 ∧ 0 ≤ Y j 2) →
        (∀ j < n, 2 ≤ Y j 0 ∧ Y j 1 ≤ ε / Y j 0 ∧ Y j 2 ≤ ε / Y j 0) →
        (∀ j < n, ∀ i : Fin 2,
          Y (j + 1) i.succ ≤ coreReturnState coreRadiusReturnTime (Y j) i.succ) →
        (∀ p : ℝ, 0 < p → ∀ i : Fin 2,
          ∑ j ∈ Finset.range n, Y j i.succ ^ p / Y j 0 ≤
            (1 + p * c / 2) / (p * c) * (Y 0 i.succ ^ p - Y n i.succ ^ p)) ∧
          ∀ p : ℝ, 0 < p →
            ∑ j ∈ Finset.range n, (Y j 1 + Y j 2) ^ p / Y j 0 ≤
              (1 + p * c / 2) / (p * c) * ((Y 0 1 + Y 0 2) ^ p - (Y n 1 + Y n 2) ^ p) := by
  obtain ⟨ε, hε, hεmax, c, hc, hcmax, H⟩ := exists_coreRadiusReturn_uniform_contraction
  refine ⟨ε, hε, hεmax, c, hc, hcmax, ?_⟩
  intro n Y hpos hentry hconn
  have HW (j : ℕ) (hj : j < n) :=
    (H (Y j) (hentry j hj).1 ⟨(hpos j hj.le).1, (hentry j hj).2.1⟩
      ⟨(hpos j hj.le).2, (hentry j hj).2.2⟩).2.2.2
  constructor
  · intro p hp i
    have hi (j : ℕ) (hj : j ≤ n) : 0 ≤ Y j i.succ := by
      fin_cases i
      · exact (hpos j hj).1
      · exact (hpos j hj).2
    exact sum_rpow_div_le_core_losses (b := fun j => coreReturnState coreRadiusReturnTime (Y j) i.succ)
      hc hp n hi (fun j hj => (hentry j hj).1)
      (fun j hj => (HW j hj i).2.2) (fun j hj => hconn j hj i)
  · intro p hp
    apply sum_rpow_div_le_core_losses
      (b := fun j => coreReturnState coreRadiusReturnTime (Y j) 1 +
        coreReturnState coreRadiusReturnTime (Y j) 2) hc hp n
      (fun j hj => add_nonneg (hpos j hj).1 (hpos j hj).2) (fun j hj => (hentry j hj).1)
    · intro j hj
      simpa only [mul_add] using! add_le_add (HW j hj 0).2.2 (HW j hj 1).2.2
    · intro j hj
      exact add_le_add (hconn j hj 0) (hconn j hj 1)

end BianchiIX
