import BianchiIX.Dynamics.EntranceMultiplierBounds
import BianchiIX.Dynamics.EntranceReturnDecay

noncomputable section

namespace BianchiIX

theorem entranceReturnMultiplier_decay_nonneg {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    let k := coreRadius (y 0) (y 2)
    let L := -Real.log (y 2)
    entranceReturnMultiplier y 0 ≤ y 2 * Real.exp (-k * L / 3) ∧
      entranceReturnMultiplier y 2 ≤ y 2 * Real.exp (-L / k) := by
  intro k L
  have H (z : ProjectiveState) (h0 : z 0 = y 0) (h2 : z 2 = y 2)
      (hu : 0 < z 1 ∧ z 1 ≤ 1 / 10000) (hw : 0 < z 3 ∧ z 3 ≤ 1 / 10000) :
      entranceReturnMultiplier z 0 ≤ y 2 * Real.exp (-k * L / 3) ∧
        entranceReturnMultiplier z 2 ≤ y 2 * Real.exp (-L / k) := by
    have hk' : 7 / 4 ≤ coreRadius (z 0) (z 2) := by simpa only [h0, h2] using hk
    have hm' : 1 ≤ z 0 := by simpa only [h0] using hm
    have hv' : 0 < z 2 ∧ z 2 < 1 := by simpa only [h2] using hv
    have hu' := And.intro hu.1.le hu.2
    have hw' := And.intro hw.1.le hw.2
    have hd := entrance_initial_denom_pos hk' hm' hu' hv' hw'
    have hr := (entranceReturn_regular hk' hm' hu' hv' hw').1
    have hdec := entranceReturn_decay hk' hm' hu' hv' hw'
    have hfacU : entranceReturnState z 1 = z 1 * entranceReturnMultiplier z 0 :=
      entranceReturn_wall_factorization hd hr 0
    have hfacW : entranceReturnState z 3 = z 3 * entranceReturnMultiplier z 2 :=
      entranceReturn_wall_factorization hd hr 2
    have hU : z 1 * entranceReturnMultiplier z 0 ≤ z 1 * (y 2 * Real.exp (-k * L / 3)) := by
      rw [← hfacU]
      simpa only [h0, h2, mul_assoc] using hdec.1
    have hW : z 3 * entranceReturnMultiplier z 2 ≤ z 3 * (y 2 * Real.exp (-L / k)) := by
      rw [← hfacW]
      simpa only [h0, h2, mul_assoc] using hdec.2
    exact ⟨le_of_mul_le_mul_left hU hu.1, le_of_mul_le_mul_left hW hw.1⟩
  exact ⟨le_of_two_nonnegative_walls (by norm_num) hu hw
      (entranceReturnMultiplier_regular hk hm hu hv hw 0).1.continuousAt
      (fun z h0 h2 hu hw => (H z h0 h2 hu hw).1),
    le_of_two_nonnegative_walls (by norm_num) hu hw
      (entranceReturnMultiplier_regular hk hm hu hv hw 2).1.continuousAt
      (fun z h0 h2 hu hw => (H z h0 h2 hu hw).2)⟩

theorem EntranceRadialInverseAt.return_wall_multiplier_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (i : Fin 3) (d : ProjectiveState) :
    fderiv ℝ (fun z => entranceReturnState (Ψ z)) (entranceRadialCoordinates y) d i.succ =
      entranceReturnMultiplier y i * (d i.succ + y i.succ * entranceLogMultiplierResponse y i d) := by
  let v := entranceRadialInverseDifferential y d
  have hv' : v i.succ = d i.succ := by
    fin_cases i <;> simp [v, entranceRadialInverseDifferential_apply]
  have hΛ := (entranceReturnMultiplier_regular hk hm hu hv hw i).1.differentiableAt (by norm_num)
  have hΛ0 := (entranceReturnMultiplier_pos y i).ne'
  have hl : entranceLogMultiplierResponse y i d =
      (entranceReturnMultiplier y i)⁻¹ * fderiv ℝ (fun z => entranceReturnMultiplier z i) y v := by
    unfold entranceLogMultiplierResponse
    rw [ContinuousLinearMap.comp_apply, (hΛ.hasFDerivAt.log hΛ0).fderiv]
    rfl
  rw [(HΨ.hasFDerivAt_return hk hm hu hv hw).fderiv, ContinuousLinearMap.comp_apply,
    entranceReturn_wall_differential hk hm hu hv hw]
  change v i.succ * entranceReturnMultiplier y i +
    y i.succ * fderiv ℝ (fun z => entranceReturnMultiplier z i) y v = _
  rw [hv', hl]
  field_simp

/-- The actual first arrival has amplitude-preserving ordinary derivatives at both zero walls. -/
theorem exists_entrance_wall_response_nonneg :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      7 / 4 ≤ coreRadius (y 0) (y 2) → 1 ≤ y 0 → (0 ≤ y 1 ∧ y 1 ≤ ε) →
      (0 < y 2 ∧ y 2 < 1) → (0 ≤ y 3 ∧ y 3 ≤ ε) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      ContDiffAt ℝ 2 (fun z => entranceReturnState (Ψ z)) (entranceRadialCoordinates y) ∧
      ∀ d : ProjectiveState,
      let J := fderiv ℝ (fun z => entranceReturnState (Ψ z)) (entranceRadialCoordinates y) d
      let k := coreRadius (y 0) (y 2)
      let L := -Real.log (y 2)
      |J 1| ≤ y 2 * Real.exp (-k * L / 3) *
        (|d 1| + C * y 1 * entranceStrongResponseWeight y d) ∧
      |J 3| ≤ y 2 * Real.exp (-L / k) *
        (|d 3| + C * y 3 * entranceWeakResponseWeight y d) := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_logMultiplier_weighted_bounds
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y hk hm hu hv hw
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hεsmall⟩
  have hy : entranceRegion (coreRadius (y 0) (y 2)) y :=
    ⟨hm, by simp; positivity, hu', ⟨hv.1.le, hv.2.le⟩, hw'⟩
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk hy hv.1
  have hF : ContDiffAt ℝ 2 entranceReturnState (Ψ (entranceRadialCoordinates y)) := by
    rw [HΨ.apply_base]
    exact (entranceReturn_regular hk hm hu' hv hw').2.2.1
  refine ⟨Ψ, HΨ, hF.comp _ HΨ.contDiffAt, ?_⟩
  intro d
  dsimp only
  have H := HC y hk hm hu hv hw d
  have hdec := entranceReturnMultiplier_decay_nonneg hk hm hu' hv hw'
  have bound {a u r Λ E W : ℝ} (hu : 0 ≤ u) (hΛ : 0 < Λ) (hE : Λ ≤ E)
      (hW : 0 ≤ W) (hr : |r| ≤ C * W) :
      |Λ * (a + u * r)| ≤ E * (|a| + C * u * W) := by
    rw [abs_mul, abs_of_pos hΛ]
    have hsum : |a + u * r| ≤ |a| + C * u * W := by
      calc
        _ ≤ |a| + |u * r| := abs_add_le _ _
        _ = |a| + u * |r| := by rw [abs_mul, abs_of_nonneg hu]
        _ ≤ |a| + C * u * W := by nlinarith only [mul_le_mul_of_nonneg_left hr hu]
    exact mul_le_mul hE hsum (abs_nonneg _) (hΛ.le.trans hE)
  constructor
  · have hJU : fderiv ℝ (fun z => entranceReturnState (Ψ z))
          (entranceRadialCoordinates y) d 1 = entranceReturnMultiplier y 0 *
          (d 1 + y 1 * entranceLogMultiplierResponse y 0 d) :=
      HΨ.return_wall_multiplier_differential hk hm hu' hv hw' 0 d
    rw [hJU]
    exact bound hu.1 (entranceReturnMultiplier_pos y 0) hdec.1
      (entranceResponseWeights_nonneg hv d).1 H.1
  · have hJW : fderiv ℝ (fun z => entranceReturnState (Ψ z))
          (entranceRadialCoordinates y) d 3 = entranceReturnMultiplier y 2 *
          (d 3 + y 3 * entranceLogMultiplierResponse y 2 d) :=
      HΨ.return_wall_multiplier_differential hk hm hu' hv hw' 2 d
    rw [hJW]
    exact bound hw.1 (entranceReturnMultiplier_pos y 2) hdec.2
      (entranceResponseWeights_nonneg hv d).2 H.2

end BianchiIX
