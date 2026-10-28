import BianchiIX.Dynamics.EntranceLogWallDirections

noncomputable section

namespace BianchiIX

open Set

/-- All four input coordinates may move; logarithmic output bounds retain the actual wall amplitudes. -/
theorem exists_entrance_wall_direction_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      let L := -Real.log (y 2)
      let z := entranceReturnState y
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → ContDiffAt ℝ 2 entranceReturnState y ∧ 0 < z 1 ∧ 0 < z 3 ∧
      ∀ (D : ℝ) (d : ProjectiveState), 0 ≤ D → |d 0| ≤ D * k ^ 2 →
        (∀ i : Fin 4, i ≠ 0 → |d i| ≤ D * k * y i) →
        |fderiv ℝ entranceReturnState y d 1| ≤ C * D * k ^ 2 * (1 + L) * z 1 ∧
        |fderiv ℝ entranceReturnState y d 3| ≤ C * D * (k + L) * z 3 := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_return_full_columns
  obtain ⟨B, hB, HB⟩ := exists_entrance_radius_input_direction_bounds
  refine ⟨(3 * A + 1) * (B + 2), by positivity, ε, hε, hεsmall, ?_⟩
  intro y k L z hk hm hu hv hw
  have hk0 : 0 < k := by linarith only [hk]
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have hy : entranceRegion k y := ⟨hm, by change |k - k| ≤ k / 100; simp only [sub_self, abs_zero]; positivity,
    hu', ⟨hv.1.le, hv.2.le⟩, hw'⟩
  have HR := entranceReturn_regular hk hm hu' hv hw'
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have HP := entranceReturn_walls_pos hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ _ ht
  have hZu : 0 < z 1 := HP.1
  have hZw : 0 < z 3 := HP.2.2
  obtain ⟨Ψ, HΨ, _, HS, HT⟩ := HA y 1 hk hm hu hv hw (Or.inl rfl)
  let f := fun p => entranceLogWalls 1 (entranceReturnState p)
  let F := fun p => entranceLogWalls 1 (entranceReturnState (Ψ p))
  let x := entranceRadialCoordinates y
  have Hf := ((hasFDerivAt_entranceLogWalls 1 hZu.ne' hZw.ne').differentiableAt.hasFDerivAt).comp y
    (HR.2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt f _ y at Hf
  have HF : HasFDerivAt F ((fderiv ℝ f y).comp (entranceRadialInverseDifferential y)) x := by
    have Hf' : HasFDerivAt f (fderiv ℝ f y) (Ψ x) := by rw [show Ψ x = y from HΨ.apply_base]; exact Hf.differentiableAt.hasFDerivAt
    exact Hf'.comp x HΨ.hasFDerivAt
  have Htransfer (d : ProjectiveState) : fderiv ℝ F x (entranceRadialDifferential y d) =
      entranceWallTangent 1 z (fderiv ℝ entranceReturnState y d) := by
    rw [HF.fderiv, ContinuousLinearMap.comp_apply, (entranceRegion_radialDifferential_inverse hk hy hv.1).1,
      Hf.fderiv, ContinuousLinearMap.comp_apply]
    exact entranceLogWalls_fderiv_apply 1 hZu.ne' hZw.ne' _
  refine ⟨HR.2.2.1, hZu, hZw, ?_⟩
  intro D d hD hd0 hdwall
  let v := entranceRadialDifferential y d
  let S := (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ F x)
  let T := (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ F x)
  have hv0 : |v 0| ≤ ((B + 2) * D) * k ^ 2 := (HB k y hk hy hv.1).2 D d hD hd0 hdwall |>.2
  have hvwall (i : Fin 4) (hi : i ≠ 0) : |v i| ≤ ((B + 2) * D) * k * y i := by
    have heq : v i = d i := by
      fin_cases i
      · exact (hi rfl).elim
      · rfl
      · rfl
      · rfl
    have hyi : 0 ≤ y i := by
      fin_cases i
      · exact (hi rfl).elim
      · exact hu.1.le
      · exact hv.1.le
      · exact hw.1.le
    rw [heq]
    exact (hdwall i hi).trans (by
      have H := mul_nonneg (show 0 ≤ B + 1 by linarith only [hB]) (mul_nonneg (mul_nonneg hD hk0.le) hyi)
      nlinarith only [H])
  have Hlog := entrance_logWall_columns_direction (S := S) (T := T) (d := v) hA.le
    (by positivity : 0 ≤ (B + 2) * D) (by linarith only [hk])
    (neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le))
    ⟨hu.1, by linarith only [hu'.2]⟩ hv.1 ⟨hw.1, by linarith only [hw'.2]⟩
    HS.1 HS.2.1 HS.2.2.1 HS.2.2.2 HT.1 HT.2.1 HT.2.2.1 HT.2.2.2
    hv0 (hvwall 1 (by decide)) (hvwall 2 (by decide)) (hvwall 3 (by decide))
  change |fderiv ℝ F x v 0| ≤ _ ∧ |fderiv ℝ F x v 1| ≤ _ at Hlog
  rw [show v = entranceRadialDifferential y d from rfl, Htransfer] at Hlog
  change |fderiv ℝ entranceReturnState y d 1 / z 1| ≤ _ ∧
    |(1 : ℝ) ^ 2 * (fderiv ℝ entranceReturnState y d 3 / z 3)| ≤ _ at Hlog
  simp only [one_pow, one_mul, abs_div, abs_of_pos hZu, abs_of_pos hZw] at Hlog
  constructor
  · exact ((div_le_iff₀ hZu).mp Hlog.1).trans_eq (by ring)
  · exact ((div_le_iff₀ hZw).mp Hlog.2).trans_eq (by ring)

end BianchiIX
