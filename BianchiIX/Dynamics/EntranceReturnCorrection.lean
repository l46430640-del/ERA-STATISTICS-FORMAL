import BianchiIX.Dynamics.EntranceRadiusCorrectionVariation

noncomputable section

namespace BianchiIX

open Set

/-- The actual moving arrival correction retains the terminal wall amplitudes in each derivative. -/
theorem exists_entrance_return_correction_variation :
    ∃ C > (0 : ℝ), ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ 1 / 10000) →
      (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ 1 / 10000) →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
      let z := entranceRadialCoordinates y
      let p := entranceReturnState y
      let b := p 1 + p 3
      let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
      let L := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
      let E := fun z => entranceRadiusCorrection (entranceReturnState (Ψ z))
      ∀ d : ProjectiveState,
      |fderiv ℝ E z d| ≤ C *
        (b ^ 2 / k ^ 2 * |fderiv ℝ Q z d| +
          b / k * (p 1 * |fderiv ℝ L z d 0| + p 3 * |fderiv ℝ L z d 1|)) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceRadiusCorrection_variation_bound
  refine ⟨C, hC, ?_⟩
  intro y k hk hm hu hv hw Ψ HΨ z p b Q L E d
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2⟩
  have HR := entranceReturn_regular hk hm hu' hv hw'
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have hp : entranceRegion k p := entranceReturn_region hk hm hu' hv hw' _ ht
  have hpos : 0 < p 1 ∧ 0 < p 2 ∧ 0 < p 3 := entranceReturn_walls_pos hk hm hu hv hw _ ht
  have hM : 2 ≤ p 0 := by linarith [(entranceRegion_phase hk hp).1]
  have hU : |p 1| < 1 / 200 := by rw [abs_of_nonneg hp.2.2.1.1]; linarith [hp.2.2.1.2]
  have hW : |p 3| < 1 / 200 := by rw [abs_of_nonneg hp.2.2.2.2.1]; linarith [hp.2.2.2.2.2]
  let g := fun z => entranceReturnState (Ψ z)
  let ξ := fderiv ℝ g z d
  have hg := HΨ.hasFDerivAt_return hk hm hu' hv hw'
  have hbase : g z = p := by dsimp [g, z, p]; rw [HΨ.apply_base]
  have hξ : ξ 2 = 0 := by
    dsimp [ξ, g, z]
    rw [hg.fderiv, ContinuousLinearMap.comp_apply]
    exact (entranceReturn_active_component hk hm hu' hv hw').2 _
  have hscalar (f : ProjectiveState → ℝ) (hf : DifferentiableAt ℝ f p) :
      fderiv ℝ (fun z => f (g z)) z d = fderiv ℝ f p ξ := by
    have hf' : HasFDerivAt f (fderiv ℝ f p) (g z) := by rw [hbase]; exact hf.hasFDerivAt
    have H := hf'.comp z hg.differentiableAt.hasFDerivAt
    simp only [Function.comp_def] at H
    rw [H.fderiv, ContinuousLinearMap.comp_apply]
  have hQ : fderiv ℝ Q z d = fderiv ℝ entranceStableRadius p ξ :=
    hscalar _ ((contDiffAt_entranceStableRadius_two hM hU hW hpos.2.1).differentiableAt (by norm_num))
  have hE : fderiv ℝ E z d = fderiv ℝ entranceRadiusCorrection p ξ :=
    hscalar _ ((contDiffAt_entranceRadiusCorrection_two hM hU hW hpos.2.1).differentiableAt (by norm_num))
  have hL : fderiv ℝ L z d = ![ξ 1 / p 1, ξ 3 / p 3] := by
    have hf : HasFDerivAt (entranceLogWalls 1) (fderiv ℝ (entranceLogWalls 1) p) (g z) := by
      rw [hbase]
      exact (hasFDerivAt_entranceLogWalls 1 hpos.1.ne' hpos.2.2.ne').differentiableAt.hasFDerivAt
    have H := hf.comp z hg.differentiableAt.hasFDerivAt
    simp only [Function.comp_def] at H
    change HasFDerivAt L _ z at H
    rw [H.fderiv, ContinuousLinearMap.comp_apply, entranceLogWalls_fderiv_apply 1 hpos.1.ne' hpos.2.2.ne']
    simp [entranceWallTangent, ξ, g, z]
  have hUabs : p 1 * |fderiv ℝ L z d 0| = |ξ 1| := by
    rw [hL]
    simp only [Matrix.cons_val_zero, abs_div, abs_of_pos hpos.1]
    field_simp [hpos.1.ne']
  have hWabs : p 3 * |fderiv ℝ L z d 1| = |ξ 3| := by
    rw [hL]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, abs_div, abs_of_pos hpos.2.2]
    field_simp [hpos.2.2.ne']
  rw [hE, hQ, hUabs, hWabs]
  exact HC k p hk hp hpos.2.1 ξ hξ

end BianchiIX
