import BianchiIX.Dynamics.EntranceSinglePhaseCorrection
import BianchiIX.Dynamics.ExitCycleHeightUniform

noncomputable section

namespace BianchiIX

/-- The full stable-projection correction (D.29) at the canonical terminal endpoint. -/
theorem exists_terminal_stable_projection_bounds {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 40000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := projectiveCycle (coreTailState h Y)
      let s := stableRestriction z
      let β := |z 1| + |z 3|
      let D := fun p : StableState => stableBoundaryProjection (p 0) (p 1) (p 2) -
        singleStrongUpperRoot (singleStrongInvariant (p 0) (p 1))
      let e := entranceStableRadius z - (singleStrongUpperRoot (singleStrongInvariant (z 0) (z 1)) - 1)
      coreTailValid h Y ∧ ContDiffAt ℝ 2 D s ∧
        |D s| ≤ C * α * |z 3| * β ∧
        |fderiv ℝ D s (Pi.single 0 1)| ≤ C * α ^ 2 * |z 3| * β ∧
        |fderiv ℝ D s (Pi.single 1 1)| ≤ C * α * |z 3| ∧
        |fderiv ℝ D s (Pi.single 2 1)| ≤ C * α * β ∧
        e = D s + (z 2) ^ 2 / (entranceStableRadius z + entranceStablePhase z - 1) ∧
        |e| ≤ C * α * (|z 3| * β + (z 2) ^ 2) := by
  obtain ⟨A, hA, HA⟩ := exists_stableStrongProjectionError_scaled_bounds
  obtain ⟨B, hB, HB⟩ := exists_entranceSinglePhaseError_scaled_bounds
  obtain ⟨K, hK, ε₀, hε₀, HG⟩ := exists_terminal_axisCycle_endpoint_uniform
    ⟨hη₀.1, hη₀.2.trans (by norm_num)⟩ hJ
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let ε := min ε₀ (1 / (20000 * K))
  refine ⟨A + B + 1, by linarith only [hA, hB], ε, lt_min hε₀ (by positivity), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h z s β D e
  have hα0 := hα.1
  have hη0 : 0 < η := hη₀.1.trans_le hηlo
  have hsg := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, _, _, HM, _, HU, HW, _, _, _⟩ :=
    HG η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsg hsum
  change 19 / (10 * α) < z 0 - 1 ∧ z 0 - 1 < 21 / (10 * α) at HM
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at HU
  change |z 2| ≤ 2 * (K * b) / α ^ 2 ∧ |z 3| ≤ 2 * (K * b) / α ^ 2 at HW
  have Hlow : 1 / α ≤ 19 / (10 * α) := by
    apply (div_le_div_iff₀ hα.1 (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.1]
  have hscale : 1 / α ≤ z 0 + 1 := by linarith only [Hlow, HM.1]
  have hone : 1 ≤ 1 / α := (le_div_iff₀ hα.1).mpr (by simpa using hα.2)
  have hm : 2 ≤ z 0 := by linarith only [hone, Hlow, HM.1]
  have hu : |z 1| ≤ 1 / 10000 := by
    have hU0 : 0 ≤ z 1 := (by positivity : 0 ≤ η / 2 * α ^ (J - 2)).trans HU.1
    rw [abs_of_nonneg hU0]
    have Hpow := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J - 2)) (by positivity : 0 ≤ 2 * η)
    nlinarith only [HU.2, Hpow, hηhi]
  have Hbudget : 2 * (K * b) ≤ α ^ 2 / 10000 := by
    have Hε := (le_div_iff₀ (by positivity : 0 < 20000 * K)).mp (min_le_right ε₀ (1 / (20000 * K)))
    have Hpow := pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)
    have H1 := mul_le_mul_of_nonneg_left hsmall hK0.le
    have H2 := mul_le_mul_of_nonneg_right Hε (pow_nonneg hα.1.le (2 * J))
    nlinarith only [H1, H2, Hpow]
  have hw : |z 3| ≤ 1 / 10000 := HW.2.trans ((div_le_iff₀ (sq_pos_of_pos hα.1)).mpr (by linarith only [Hbudget]))
  have hu' : |z 1| < 1 / 200 := by linarith only [hu]
  have hw' : |z 3| < 1 / 200 := by linarith only [hw]
  have H0 := HA α s hα.1 hscale hm hu' hw'
  have H1 := HB α z hα.1 hscale hm hu hw
  have HE := stableStrongProjectionError_eventuallyEq_single (y := s) hm hu'
  change stableStrongProjectionError =ᶠ[nhds s] D at HE
  have HD : fderiv ℝ stableStrongProjectionError s = fderiv ℝ D s := HE.fderiv_eq
  rw [HE.eq_of_nhds, HD] at H0
  change |D s| ≤ A * α * |z 3| * β ∧
    |fderiv ℝ D s (Pi.single 0 1)| ≤ A * α ^ 2 * |z 3| * β ∧
    |fderiv ℝ D s (Pi.single 1 1)| ≤ A * α * |z 3| ∧
    |fderiv ℝ D s (Pi.single 2 1)| ≤ A * α * β at H0
  have HR := (stableStrongProjectionError_differential (y := s) hm hu' hw').1.congr_of_eventuallyEq HE.symm
  have Heq : entranceSinglePhaseError z = e := entranceSinglePhaseError_eq hm (hu'.le)
  rw [Heq] at H1
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hlarge (a c : ℝ) (hc : 0 ≤ c) (ha : a ≤ A + B + 1) : a * c ≤ (A + B + 1) * c :=
    mul_le_mul_of_nonneg_right ha hc
  refine ⟨HV, HR, H0.1.trans ?_, H0.2.1.trans ?_, H0.2.2.1.trans ?_, H0.2.2.2.trans ?_, ?_, H1.trans ?_⟩
  · nlinarith only [hlarge A (α * |z 3| * β) (by positivity) (by linarith only [hB])]
  · nlinarith only [hlarge A (α ^ 2 * |z 3| * β) (by positivity) (by linarith only [hB])]
  · nlinarith only [hlarge A (α * |z 3|) (by positivity) (by linarith only [hB])]
  · nlinarith only [hlarge A (α * β) (by positivity) (by linarith only [hB])]
  · have H := entranceSinglePhaseError_decomposition (entranceStablePhase_large_lower hm hu hw).2
    rw [Heq, HE.eq_of_nhds] at H
    exact H
  · nlinarith only [hlarge B (α * (|z 3| * β + (z 2) ^ 2)) (by positivity) (by linarith only [hA])]

end BianchiIX
