import BianchiIX.Dynamics.EntranceRadialInputResponse

noncomputable section

namespace BianchiIX

/-- Entrance changes the physical radius by a small, weighted amount in value and derivative. -/
theorem exists_entrance_physical_radial_response :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      let R := fun p : ProjectiveState => coreRadius (entranceReturnState p 0) (entranceReturnState p 2)
      let K := fun p : ProjectiveState => coreRadius (p 0) (p 2)
      let b := y 1 + y 3
      let H := y 1 * y 2 + (y 2) ^ 2 * b ^ 2
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) →
      ContDiffAt ℝ 2 R y ∧ |R y - k| ≤ C * (b ^ 2 + H) / k ∧
      ∀ (D : ℝ) (d : ProjectiveState), 0 ≤ D → |d 0| ≤ D * k ^ 2 →
        (∀ i : Fin 4, i ≠ 0 → |d i| ≤ D * k * y i) →
        |fderiv ℝ R y d - fderiv ℝ K y d| ≤ C * D * (b ^ 2 + k * H) := by
  obtain ⟨A, hA, HA⟩ := exists_entrance_radius_input_direction_bounds
  obtain ⟨B, hB, ε, hε, hεsmall, HB⟩ := exists_entrance_physical_direction_bounds
  let C := A + B * (A + 2)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hAC : A ≤ C := le_add_of_nonneg_right (by positivity)
  have hBC : B ≤ C := by dsimp only [C]; nlinarith only [hA, hB, mul_pos hA hB]
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y k R K b H hk hm hu hv hw
  have hk0 : 0 < k := by linarith only [hk]
  have hreg : entranceRegion k y := ⟨hm, by change |k - k| ≤ k / 100; simp only [sub_self, abs_zero]; positivity,
    ⟨hu.1.le, hu.2.trans hεsmall⟩, ⟨hv.1.le, hv.2.le⟩, ⟨hw.1.le, hw.2.trans hεsmall⟩⟩
  have hm2 : 2 ≤ y 0 := by linarith only [(entranceRegion_phase hk hreg).1, hk]
  obtain ⟨Hinput, HDinput⟩ := HA k y hk hreg hv.1
  obtain ⟨HR, Hreturn, HDreturn⟩ := HB y hk hm2 hu hv hw
  have hH : 0 ≤ H := by dsimp only [H]; positivity [hu.1, hv.1]
  refine ⟨HR, ?_, ?_⟩
  · calc
      _ ≤ |R y - entranceStableRadius y| + |entranceStableRadius y - k| := abs_sub_le _ _ _
      _ ≤ B * H / k + A * b ^ 2 / k := add_le_add Hreturn Hinput
      _ ≤ C * H / k + C * b ^ 2 / k := by gcongr
      _ = _ := by ring
  · intro D d hD hd0 hdwall
    obtain ⟨HI, HIbound⟩ := HDinput D d hD hd0 hdwall
    have hD' : 0 ≤ (A + 2) * D := by positivity
    have hwall' (i : Fin 4) (hi : i ≠ 0) : |d i| ≤ ((A + 2) * D) * k * y i := by
      have hyi : 0 ≤ y i := by fin_cases i <;> simp_all only <;> positivity [hu.1, hv.1, hw.1]
      have hmono : 0 ≤ (A + 1) * (D * k * y i) := mul_nonneg (by linarith only [hA])
        (mul_nonneg (mul_nonneg hD hk0.le) hyi)
      exact (hdwall i hi).trans (by nlinarith only [hmono])
    have HO := HDreturn ((A + 2) * D) d hD' HIbound hwall'
    calc
      _ ≤ |fderiv ℝ R y d - fderiv ℝ entranceStableRadius y d| +
          |fderiv ℝ entranceStableRadius y d - fderiv ℝ K y d| := abs_sub_le _ _ _
      _ ≤ B * ((A + 2) * D) * k * H + A * D * b ^ 2 := add_le_add HO HI
      _ ≤ C * D * (b ^ 2 + k * H) := by
        dsimp only [C]
        nlinarith only [mul_nonneg (mul_nonneg hA.le hD) (mul_nonneg hk0.le hH),
          mul_nonneg (by positivity : 0 ≤ B * (A + 2) * D) (sq_nonneg b)]

/-- The same estimates apply to an arbitrary differentiable family of exact entrance data. -/
theorem exists_entrance_physical_curve_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (Y : ℝ → ProjectiveState) (ρ D : ℝ),
      let y := Y ρ
      let k := coreRadius (y 0) (y 2)
      let κ := fun t => coreRadius (entranceReturnState (Y t) 0) (entranceReturnState (Y t) 2)
      let K := fun t => coreRadius (Y t 0) (Y t 2)
      let b := y 1 + y 3
      let H := y 1 * y 2 + (y 2) ^ 2 * b ^ 2
      DifferentiableAt ℝ Y ρ → 0 ≤ D → 7 / 4 ≤ k → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ ε) →
      |deriv (fun t => Y t 0) ρ| ≤ D * k ^ 2 →
      (∀ i : Fin 4, i ≠ 0 → |deriv (fun t => Y t i) ρ| ≤ D * k * y i) →
      DifferentiableAt ℝ κ ρ ∧ DifferentiableAt ℝ K ρ ∧
      |κ ρ - k| ≤ C * (b ^ 2 + H) / k ∧ |deriv κ ρ - deriv K ρ| ≤ C * D * (b ^ 2 + k * H) := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_physical_radial_response
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro Y ρ D y k κ K b H HY hD hk hm hu hv hw hd0 hdwall
  obtain ⟨HR, Hval, HD⟩ := HC y hk hm hu hv hw
  have Hκ := (HR.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt ρ HY.hasDerivAt
  have HK := (hasFDerivAt_coreRadius_state hv.1).differentiableAt.hasFDerivAt.comp_hasDerivAt ρ HY.hasDerivAt
  change HasDerivAt κ _ ρ at Hκ
  change HasDerivAt K _ ρ at HK
  have hcomponent (i : Fin 4) : deriv Y ρ i = deriv (fun t => Y t i) ρ :=
    (hasDerivAt_pi.mp HY.hasDerivAt i).deriv.symm
  refine ⟨Hκ.differentiableAt, HK.differentiableAt, Hval, ?_⟩
  rw [Hκ.deriv, HK.deriv]
  exact HD D (deriv Y ρ) hD (by simpa only [hcomponent] using hd0)
    (fun i hi => by simpa only [hcomponent] using hdwall i hi)

end BianchiIX
