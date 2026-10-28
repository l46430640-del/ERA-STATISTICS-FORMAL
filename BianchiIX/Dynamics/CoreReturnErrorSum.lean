import BianchiIX.Dynamics.CoreReturnEstimates
import BianchiIX.Analysis.DiscreteDissipation

noncomputable section

namespace BianchiIX

/-- Core phase and logarithmic errors have length-independent budgets along any admissible sequence with no amplitude gain between cores. -/
theorem exists_coreRadiusReturn_error_sums :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ (n : ℕ) (Y v : ℕ → CoreAngleState),
        (∀ j ≤ n, 0 ≤ Y j 1 ∧ 0 ≤ Y j 2) →
        (∀ j < n, 2 ≤ Y j 0 ∧ Y j 1 ≤ ε / Y j 0 ∧ Y j 2 ≤ ε / Y j 0) →
        (∀ j < n, Y (j + 1) 1 + Y (j + 1) 2 ≤
          coreReturnState coreRadiusReturnTime (Y j) 1 + coreReturnState coreRadiusReturnTime (Y j) 2) →
        (∀ j < n, v j 0 = 1 ∧ |v j 1| ≤ Real.sqrt (Y j 1) ∧ |v j 2| ≤ Real.sqrt (Y j 2)) →
        let F := coreReturnState coreRadiusReturnTime
        let b := fun j => Y j 1 + Y j 2
        (∑ j ∈ Finset.range n, |F (Y j) 0 - Y j 0|) ≤
          C * ((1 + c / 2) / c) * (b 0 - b n) ∧
        (∑ j ∈ Finset.range n, |Real.log (fderiv ℝ F (Y j) (v j) 0)|) ≤
          C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n)) := by
  obtain ⟨ε, hε, hεmax, C, hC, c, hc, hcmax, H⟩ := exists_coreRadiusReturn_estimates
  refine ⟨ε, hε, hεmax, C, hC, c, hc, hcmax, ?_⟩
  intro n Y v hpos hentry hconn hcone F b
  have HE (j : ℕ) (hj : j < n) := H (Y j) (hentry j hj).1
    ⟨(hpos j hj.le).1, (hentry j hj).2.1⟩ ⟨(hpos j hj.le).2, (hentry j hj).2.2⟩
  have hnonneg (j : ℕ) (hj : j ≤ n) : 0 ≤ b j :=
    add_nonneg (hpos j hj).1 (hpos j hj).2
  have hdec (j : ℕ) (hj : j < n) : F (Y j) 1 + F (Y j) 2 ≤ Real.exp (-c / Y j 0) * b j := by
    obtain ⟨_, _, _, _, hwalls, _⟩ := HE j hj
    simpa only [b, F, mul_add] using! add_le_add (hwalls 0).2.2 (hwalls 1).2.2
  have hbudget (p : ℝ) (hp : 0 < p) := sum_rpow_div_le_core_losses
    (a := b) (b := fun j => F (Y j) 1 + F (Y j) 2) (k := fun j => Y j 0)
    hc hp n hnonneg (fun j hj => (hentry j hj).1) hdec hconn
  have hlinear : ∑ j ∈ Finset.range n, b j / Y j 0 ≤ ((1 + c / 2) / c) * (b 0 - b n) := by
    simpa only [Real.rpow_one, one_mul] using hbudget 1 zero_lt_one
  have hroot : ∑ j ∈ Finset.range n, Real.sqrt (b j) / Y j 0 ≤
      ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n)) := by
    have Hhalf := hbudget (1 / 2) (by norm_num)
    simpa only [← Real.sqrt_eq_rpow, show (1 / 2 : ℝ) * c = c / 2 by ring,
      show c / 2 / 2 = c / 4 by ring] using Hhalf
  constructor
  · calc
      _ ≤ ∑ j ∈ Finset.range n, C * (b j / Y j 0) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (HE j (Finset.mem_range.mp hj)).2.2.2.1.trans_eq (by ring)
      _ = C * ∑ j ∈ Finset.range n, b j / Y j 0 := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (((1 + c / 2) / c) * (b 0 - b n)) := mul_le_mul_of_nonneg_left hlinear hC.le
      _ = _ := by ring
  · calc
      _ ≤ ∑ j ∈ Finset.range n, C * (Real.sqrt (b j) / Y j 0) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn := Finset.mem_range.mp hj
        obtain ⟨hv, hv1, hv2⟩ := hcone j hjn
        exact ((HE j hjn).2.2.2.2.2 (v j) hv hv1 hv2).2.1.trans_eq (by ring)
      _ = C * ∑ j ∈ Finset.range n, Real.sqrt (b j) / Y j 0 := (Finset.mul_sum _ _ _).symm
      _ ≤ C * (((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n))) :=
        mul_le_mul_of_nonneg_left hroot hC.le
      _ = _ := by ring

end BianchiIX
