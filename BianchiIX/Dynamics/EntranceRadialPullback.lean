import BianchiIX.Dynamics.EntranceRadialInverse
import BianchiIX.Dynamics.EntranceCoefficientDerivatives

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem entranceRadialInverseDifferential_columns (y : ProjectiveState) :
    entranceRadialInverseDifferential y (Pi.single 0 1) =
        (entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0)) • Pi.single 0 1 ∧
      entranceRadialInverseDifferential y (Pi.single 1 1) = Pi.single 1 1 -
        (entranceStablePartial y 1 / entranceStablePartial y 0) • Pi.single 0 1 ∧
      entranceRadialInverseDifferential y (Pi.single 2 1) = Pi.single 2 1 -
        (y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0)) • Pi.single 0 1 ∧
      entranceRadialInverseDifferential y (Pi.single 3 1) = Pi.single 3 1 -
        (entranceStablePartial y 3 / entranceStablePartial y 0) • Pi.single 0 1 := by
  repeat' constructor
  all_goals
    rw [entranceRadialInverseDifferential_apply]
    ext i
    fin_cases i <;> simp

/-- These are derivatives at fixed radial coordinates, with the other three inputs fixed. -/
theorem EntranceRadialInverseAt.scalar_partials {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) {f : ProjectiveState → ℝ} (hf : DifferentiableAt ℝ f y) :
    let z := entranceRadialCoordinates y
    let L := fderiv ℝ f y
    fderiv ℝ (fun z => f (Ψ z)) z (Pi.single 0 1) =
        entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * L (Pi.single 0 1) ∧
      fderiv ℝ (fun z => f (Ψ z)) z (Pi.single 1 1) = L (Pi.single 1 1) -
        entranceStablePartial y 1 / entranceStablePartial y 0 * L (Pi.single 0 1) ∧
      fderiv ℝ (fun z => f (Ψ z)) z (Pi.single 2 1) = L (Pi.single 2 1) -
        y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * L (Pi.single 0 1) ∧
      fderiv ℝ (fun z => f (Ψ z)) z (Pi.single 3 1) = L (Pi.single 3 1) -
        entranceStablePartial y 3 / entranceStablePartial y 0 * L (Pi.single 0 1) := by
  obtain ⟨h0, h1, h2, h3⟩ := entranceRadialInverseDifferential_columns y
  simp [H.scalar_differential hf, h0, h1, h2, h3, map_sub, map_smul, smul_eq_mul]

theorem EntranceRadialInverseAt.phase_formula {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200)
    (hw : |y 3| < 1 / 200) (hchi : 0 < entranceStablePhase y - 1) :
    ∀ᶠ z in 𝓝 (entranceRadialCoordinates y),
      entranceStablePhase (Ψ z) = 1 + Real.sqrt (z 0 ^ 2 - z 2 ^ 2) := by
  have hP : ContinuousAt entranceStablePhase (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]
    exact (contDiffAt_entranceStablePhase_two hm hu hw).continuousAt
  have hc : ContinuousAt (fun z => entranceStablePhase (Ψ z) - 1) (entranceRadialCoordinates y) :=
    (hP.comp H.contDiffAt.continuousAt).sub_const 1
  have hpos : ∀ᶠ z in 𝓝 (entranceRadialCoordinates y), 0 < entranceStablePhase (Ψ z) - 1 :=
    hc.eventually (lt_mem_nhds (by simpa only [H.apply_base] using hchi))
  filter_upwards [H.right_inverse, H.wall_coordinates, hpos] with z hz hwall hchi_z
  have hR : entranceStableRadius (Ψ z) = z 0 := by
    simpa [entranceRadialCoordinates] using congrArg (fun v : ProjectiveState => v 0) hz
  have hsq := entranceStableRadius_sq (Ψ z)
  rw [hR, hwall.2.1] at hsq
  have he : z 0 ^ 2 - z 2 ^ 2 = (entranceStablePhase (Ψ z) - 1) ^ 2 := by linarith only [hsq]
  rw [he, Real.sqrt_sq hchi_z.le]
  ring

theorem EntranceRadialInverseAt.coefficients_regular {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContDiffAt ℝ 1 (fun z => entranceRadialStrongCoefficient (Ψ z)) (entranceRadialCoordinates y) ∧
      ContDiffAt ℝ 1 (fun z => entranceRadialWeakCoefficient (Ψ z)) (entranceRadialCoordinates y) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hreg := contDiffAt_entranceRadialCoefficients_one hm hu hw hv (entranceRegion_clock_pos hk hy).ne'
  have hA : ContDiffAt ℝ 1 entranceRadialStrongCoefficient (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]; exact hreg.1
  have hB : ContDiffAt ℝ 1 entranceRadialWeakCoefficient (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]; exact hreg.2
  have hΨ := H.contDiffAt.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  exact ⟨hA.comp _ hΨ, hB.comp _ hΨ⟩

theorem entranceClockRate_fderiv (y v : ProjectiveState) :
    fderiv ℝ entranceClockRate y v =
      v 0 - (y 2 + y 3 - 2 * y 1) * v 1 - y 1 * v 2 - y 1 * v 3 := by
  have hd (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i y
  have H := ((hd 0).sub_const 1).sub ((hd 1).mul (((hd 2).add (hd 3)).sub (hd 1)))
  change HasFDerivAt entranceClockRate _ y at H
  rw [H.fderiv]
  simp only [Pi.add_apply, Pi.sub_apply, sub_apply, add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

theorem EntranceRadialInverseAt.clock_partials {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) :
    let z := entranceRadialCoordinates y
    fderiv ℝ (fun z => entranceClockRate (Ψ z)) z (Pi.single 0 1) =
        entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0) ∧
      fderiv ℝ (fun z => entranceClockRate (Ψ z)) z (Pi.single 1 1) =
        -entranceStablePartial y 1 / entranceStablePartial y 0 - (y 2 + y 3 - 2 * y 1) ∧
      fderiv ℝ (fun z => entranceClockRate (Ψ z)) z (Pi.single 2 1) =
        -y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) - y 1 ∧
      fderiv ℝ (fun z => entranceClockRate (Ψ z)) z (Pi.single 3 1) =
        -entranceStablePartial y 3 / entranceStablePartial y 0 - y 1 := by
  have hf : DifferentiableAt ℝ entranceClockRate y := by
    unfold entranceClockRate connectionSpeed coupling
    fun_prop
  simp [H.scalar_differential hf, entranceClockRate_fderiv, entranceRadialInverseDifferential_apply, neg_div]

/-- The leading radial quotient has the exact numerator used in (C.21). -/
theorem EntranceRadialInverseAt.clock_radial_cancellation {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ) :
    entranceStableRadius y *
        fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1) -
        entranceClockRate y =
      entranceStableRadius y ^ 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) -
        (y 0 - 1) + coupling (y 1) (y 2) (y 3) := by
  rw [H.clock_partials.1]
  unfold entranceClockRate connectionSpeed
  ring

end BianchiIX
