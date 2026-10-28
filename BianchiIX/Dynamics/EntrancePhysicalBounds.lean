import BianchiIX.Dynamics.EntrancePhysicalValue
import BianchiIX.Dynamics.EntrancePhysicalColumns

noncomputable section

namespace BianchiIX

theorem EntranceRadialInverseAt.physical_return_regular {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    ContDiffAt ℝ 2 (fun z => coreRadius (entranceReturnState (Ψ z) 0)
      (entranceReturnState (Ψ z) 2)) (entranceRadialCoordinates y) := by
  let z := entranceRadialCoordinates y
  have hE : ContDiffAt ℝ 2 entranceReturnState (Ψ z) := by
    rw [show Ψ z = y from HΨ.apply_base]
    exact (entranceReturn_regular hk hm hu hv hw).2.2.1
  have hP := hE.comp z HΨ.contDiffAt
  have hV : 0 < entranceReturnState y 2 := by
    rw [(entranceReturn_active_component hk hm hu hv hw).1]
    norm_num
  have hR : ContDiffAt ℝ 2 (fun p : ProjectiveState => coreRadius (p 0) (p 2))
      (entranceReturnState (Ψ z)) := by
    rw [show Ψ z = y from HΨ.apply_base]
    change ContDiffAt ℝ 2 (fun p : ProjectiveState => Real.sqrt ((p 0 - 1) ^ 2 + (p 2) ^ 2)) _
    apply ContDiffAt.sqrt (by fun_prop)
    positivity
  have H := hR.comp z hP
  exact H

/-- Equation (C.39): the value and every derivative belong to the same actual C2 return map. -/
theorem exists_entrance_physical_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let L := -Real.log (y 2)
      let ω := Real.exp (-2 * L / k)
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      ContDiffAt ℝ 2 F z ∧
      |F z - z 0| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + ω)) / k ∧
      |fderiv ℝ F z (Pi.single 0 1) - 1| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + (1 + L / k) * ω)) / k ^ 2 ∧
      |fderiv ℝ F z (Pi.single 1 1)| ≤ C * y 2 / k ∧
      |fderiv ℝ F z (Pi.single 2 1)| ≤ C * (y 1 + y 2 * (y 3) ^ 2) ∧
      |fderiv ℝ F z (Pi.single 3 1)| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * y 3 * (θ + ω)) / k := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_physical_columns
  obtain ⟨B, hB, HB⟩ := exists_entrance_physical_value_bound
  refine ⟨A + B, add_pos hA hB, ε, hε, hεsmall, ?_⟩
  intro y θ k hk hm hu hv hw hθ
  obtain ⟨Ψ, HΨ, Hr, Hu, Hv, Hw⟩ := HA y θ hk hm hu hv hw hθ
  refine ⟨Ψ, HΨ, ?_⟩
  intro z L ω F
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have H0 : |F z - z 0| ≤ B * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + ω)) / k := by
    change |coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2) - entranceStableRadius y| ≤ _
    rw [show Ψ z = y from HΨ.apply_base]
    exact HB y θ hk hm hu' hv hw' hθ
  have hk0 : 0 < k := by linarith
  have hθ0 : 0 ≤ θ := by rcases hθ with rfl | ⟨rfl, _⟩ <;> positivity
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hω : 0 ≤ ω := (Real.exp_pos _).le
  have hscale {x a b : ℝ} (ha : a ≤ A + B) (hb : 0 ≤ b) (hx : x ≤ a * b) :
      x ≤ (A + B) * b := hx.trans (mul_le_mul_of_nonneg_right ha hb)
  have hAs : A ≤ A + B := le_add_of_nonneg_right hB.le
  have hBs : B ≤ A + B := le_add_of_nonneg_left hA.le
  refine ⟨HΨ.physical_return_regular hk hm hu' hv hw', ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [mul_div_assoc] using hscale hBs
      (show 0 ≤ (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + ω)) / k by positivity [hu.1, hv.1])
      (by simpa only [mul_div_assoc] using H0)
  · simpa only [mul_div_assoc] using hscale hAs
      (show 0 ≤ (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + (1 + L / k) * ω)) / k ^ 2 by
        positivity [hu.1, hv.1]) (by simpa only [ω, L, k, mul_div_assoc] using Hr)
  · simpa only [mul_div_assoc] using hscale hAs (div_nonneg hv.1.le hk0.le)
      (by simpa only [mul_div_assoc] using Hu)
  · exact hscale hAs (by positivity [hu.1, hv.1]) Hv
  · simpa only [mul_div_assoc] using hscale hAs
      (show 0 ≤ (y 1 * y 2 + (y 2) ^ 2 * y 3 * (θ + ω)) / k by positivity [hu.1, hv.1, hw.1])
      (by simpa only [ω, L, k, mul_div_assoc] using Hw)

/-- All five inequalities of (C.25), with a common C2 physical arrival map and constants. -/
theorem exists_entrance_physical_basic_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      ContDiffAt ℝ 2 F z ∧
      |F z - z 0| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) / k ∧
      |fderiv ℝ F z (Pi.single 0 1) - 1| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) / k ^ 2 ∧
      |fderiv ℝ F z (Pi.single 1 1)| ≤ C * (y 2 + (y 2) ^ 2 * (y 1 + y 3)) / k ∧
      |fderiv ℝ F z (Pi.single 2 1)| ≤ C * (y 1 + y 2 * (y 1 + y 3) ^ 2) ∧
      |fderiv ℝ F z (Pi.single 3 1)| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3)) / k := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_physical_basic_columns
  obtain ⟨B, hB, HB⟩ := exists_entrance_physical_basic_value
  refine ⟨A + B, add_pos hA hB, ε, hε, hεsmall, ?_⟩
  intro y k hk hm hu hv hw
  obtain ⟨Ψ, HΨ, Hr, Hu, Hv, Hw⟩ := HA y hk hm hu hv hw
  refine ⟨Ψ, HΨ, ?_⟩
  intro z F
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have H0 : |F z - z 0| ≤ B * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) / k := by
    change |coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2) - entranceStableRadius y| ≤ _
    rw [show Ψ z = y from HΨ.apply_base]
    exact HB y hk hm hu' hv hw'
  have hk0 : 0 < k := by linarith
  have hscale {x a b : ℝ} (ha : a ≤ A + B) (hb : 0 ≤ b) (hx : x ≤ a * b) :
      x ≤ (A + B) * b := hx.trans (mul_le_mul_of_nonneg_right ha hb)
  have hAs : A ≤ A + B := le_add_of_nonneg_right hB.le
  have hBs : B ≤ A + B := le_add_of_nonneg_left hA.le
  refine ⟨HΨ.physical_return_regular hk hm hu' hv hw', ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [mul_div_assoc] using hscale hBs
      (show 0 ≤ (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) / k by positivity [hu.1, hv.1])
      (by simpa only [mul_div_assoc] using H0)
  · simpa only [mul_div_assoc] using hscale hAs
      (show 0 ≤ (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) / k ^ 2 by positivity [hu.1, hv.1])
      (by simpa only [mul_div_assoc] using Hr)
  · simpa only [mul_div_assoc] using hscale hAs
      (show 0 ≤ (y 2 + (y 2) ^ 2 * (y 1 + y 3)) / k by positivity [hu.1, hv.1, hw.1])
      (by simpa only [mul_div_assoc] using Hu)
  · exact hscale hAs (by positivity [hu.1, hv.1]) Hv
  · simpa only [mul_div_assoc] using hscale hAs
      (show 0 ≤ (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3)) / k by positivity [hu.1, hv.1, hw.1])
      (by simpa only [mul_div_assoc] using Hw)

end BianchiIX
