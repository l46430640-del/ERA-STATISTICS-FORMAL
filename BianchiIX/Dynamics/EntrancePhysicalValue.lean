import BianchiIX.Dynamics.EntranceRadiusDriftIntegral
import BianchiIX.Dynamics.EntranceReturnTerminalWeights
import BianchiIX.Dynamics.EntranceRadiusCorrectionBounds

noncomputable section

namespace BianchiIX

open Set

/-- The drift integral is instantiated on the canonical first arrival, including zero stable walls. -/
theorem exists_entrance_return_radius_drift :
    ∃ C > (0 : ℝ), ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      |entranceStableRadius (entranceReturnState y) - entranceStableRadius y| ≤
        C * (y 1 * y 2 + θ * (y 2 * y 3) ^ 2) / k := by
  obtain ⟨C, hC, HC⟩ := exists_scaled_entranceStableRadius_drift
  refine ⟨C, hC, ?_⟩
  intro y θ k hk hm hu hv hw hθ
  let x := fromProjectiveState y
  let Y := projectiveOriginalFlow y 0
  let a := normalizedProjectiveRate x 0
  let T := entranceReturnTime y
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint hD.ne'
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have ht : 0 ≤ T := HR.1.1.1.le
  have hinit : Y 0 = y := projectiveOriginalFlow_initial hD 0
  have hreg := entranceReturn_region hk hm hu hv hw
  have hY (r : ℝ) (hr : r ∈ Icc 0 T) : HasDerivAt Y (a r • projectiveField (Y r)) r := by
    exact hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (HR.2.1 r hr).1)
      (HR.2.1 r hr).2.ne' ((normalizedMaxCurve_constraint (HR.2.1 r hr).1).trans hc)
  have hac : ContinuousOn a (Icc 0 T) :=
    (continuousOn_normalizedProjectiveRate x 0).mono (fun r hr => (HR.2.1 r hr).1)
  have ha (r : ℝ) (hr : r ∈ Icc 0 T) : 0 ≤ a r := (HR.2.1 r hr).2.le
  have hvY (r : ℝ) (hr : r ∈ Icc 0 T) : 0 < Y r 2 := by
    apply normalized_projective_wall_pos (HR.2.1 0 ⟨le_rfl, ht⟩).1 (HR.2.1 r hr).1
      (HR.2.1 0 ⟨le_rfl, ht⟩).2 (HR.2.1 r hr).2 1
    change 0 < Y 0 2
    simpa only [hinit] using hv.1
  have H := HC Y a 0 T k θ hk ht hY hac ha hreg hvY (by simpa only [hinit] using hθ)
  simpa only [hinit, Y, T, projectiveOriginalFlow, entranceReturnState] using H

theorem exists_entrance_return_correction_value :
    ∃ C > (0 : ℝ), ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) →
      let ω := Real.exp (-2 * (-Real.log (y 2)) / k)
      |entranceRadiusCorrection (entranceReturnState y)| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * ω) / k := by
  obtain ⟨C, hC, HC⟩ := exists_entranceRadiusCorrection_bounds
  refine ⟨2 * C, by positivity, ?_⟩
  intro y k hk hm hu hv hw ω
  have hk0 : 0 < k := by linarith
  let p := entranceReturnState y
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have hp : entranceRegion k p := entranceReturn_region hk hm hu hv hw _ ⟨HR.1.1.1.le, le_rfl⟩
  have hpv : 0 < p 2 := by
    change 0 < entranceReturnState y 2
    rw [(entranceReturn_active_component hk hm hu hv hw).1]
    norm_num
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk hp hpv
  have H := (HC k p hk hp hpv Ψ HΨ).1
  have Hb := (entranceReturn_terminal_weights hk hm hu hv hw).1
  exact H.trans ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Hb hC.le) hk0.le).trans_eq
    (by ring))

/-- The zero-order physical arrival estimate of (C.39), also on zero stable walls. -/
theorem exists_entrance_physical_value_bound :
    ∃ C > (0 : ℝ), ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) →
      (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      let ω := Real.exp (-2 * (-Real.log (y 2)) / k)
      |coreRadius (entranceReturnState y 0) (entranceReturnState y 2) - entranceStableRadius y| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + ω)) / k := by
  obtain ⟨A, hA, HA⟩ := exists_entrance_return_radius_drift
  obtain ⟨B, hB, HB⟩ := exists_entrance_return_correction_value
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro y θ k hk hm hu hv hw hθ ω
  let R := y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + ω)
  have hk0 : 0 < k := by linarith
  have hθ0 : 0 ≤ θ := by rcases hθ with rfl | ⟨rfl, _⟩ <;> positivity
  have hω : 0 ≤ ω := (Real.exp_pos _).le
  have hHR : y 1 * y 2 + θ * (y 2 * y 3) ^ 2 ≤ R := by
    have H : 0 ≤ (y 2) ^ 2 * (y 3) ^ 2 * ω := by positivity
    dsimp [R]
    nlinarith only [H]
  have hJR : y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * ω ≤ R := by
    have H : 0 ≤ (y 2) ^ 2 * (y 3) ^ 2 * θ := by positivity
    dsimp [R]
    nlinarith only [H]
  have heq : coreRadius (entranceReturnState y 0) (entranceReturnState y 2) - entranceStableRadius y =
      (entranceStableRadius (entranceReturnState y) - entranceStableRadius y) -
        entranceRadiusCorrection (entranceReturnState y) := by
    unfold entranceRadiusCorrection
    ring
  rw [heq]
  calc
    _ ≤ |entranceStableRadius (entranceReturnState y) - entranceStableRadius y| +
        |entranceRadiusCorrection (entranceReturnState y)| := abs_sub _ _
    _ ≤ A * (y 1 * y 2 + θ * (y 2 * y 3) ^ 2) / k +
        B * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * ω) / k :=
      add_le_add (HA y θ hk hm hu hv hw hθ) (HB y hk hm hu hv hw)
    _ ≤ A * R / k + B * R / k := add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHR hA.le) hk0.le)
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJR hB.le) hk0.le)
    _ = _ := by dsimp [R]; ring

theorem exists_entrance_physical_basic_value :
    ∃ C > (0 : ℝ), ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) →
      |coreRadius (entranceReturnState y 0) (entranceReturnState y 2) - entranceStableRadius y| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) / k := by
  obtain ⟨C, hC, HC⟩ := exists_entrance_physical_value_bound
  refine ⟨2 * C, by positivity, ?_⟩
  intro y k hk hm hu hv hw
  apply (HC y 1 hk hm hu hv hw (Or.inl rfl)).trans
  let ω := Real.exp (-2 * (-Real.log (y 2)) / k)
  have hk0 : 0 < k := by linarith
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hω : ω ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hL]) hk0.le)
  have hsq : (y 3) ^ 2 ≤ (y 1 + y 3) ^ 2 := pow_le_pow_left₀ hw.1 (by linarith only [hu.1]) 2
  have Hsq := mul_le_mul_of_nonneg_left hsq (sq_nonneg (y 2))
  have Hω := mul_le_mul_of_nonneg_left hω (show 0 ≤ (y 2) ^ 2 * (y 3) ^ 2 by positivity)
  have Hnum : y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (1 + ω) ≤
      2 * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) := by
    nlinarith only [Hsq, Hω, mul_nonneg hu.1 hv.1.le]
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Hnum hC.le) hk0.le).trans_eq (by ring)

end BianchiIX
