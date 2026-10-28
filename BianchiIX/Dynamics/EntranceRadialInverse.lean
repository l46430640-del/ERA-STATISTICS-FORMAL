import BianchiIX.Dynamics.EntranceRadialCoordinates
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

structure EntranceRadialInverseAt (y : ProjectiveState) (Ψ : ProjectiveState → ProjectiveState) : Prop where
  apply_base : Ψ (entranceRadialCoordinates y) = y
  contDiffAt : ContDiffAt ℝ 2 Ψ (entranceRadialCoordinates y)
  hasFDerivAt : HasFDerivAt Ψ (entranceRadialInverseDifferential y) (entranceRadialCoordinates y)
  left_inverse : ∀ᶠ z in 𝓝 y, Ψ (entranceRadialCoordinates z) = z
  right_inverse : ∀ᶠ z in 𝓝 (entranceRadialCoordinates y), entranceRadialCoordinates (Ψ z) = z

theorem exists_entranceRadialInverseAt {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2)
    (hchi : entranceStablePhase y - 1 ≠ 0) (hPM : entranceStablePartial y 0 ≠ 0) :
    ∃ Ψ, EntranceRadialInverseAt y Ψ := by
  have H := entranceRadialDifferential_inverse hm hu hw hv hchi hPM
  let E : ProjectiveState ≃L[ℝ] ProjectiveState := ContinuousLinearEquiv.equivOfInverse
    (entranceRadialDifferential y) (entranceRadialInverseDifferential y) H.1 H.2
  have hc := contDiffAt_entranceRadialCoordinates_two hm hu hw hv
  have hd : HasFDerivAt entranceRadialCoordinates (E : ProjectiveState →L[ℝ] ProjectiveState) y :=
    hasFDerivAt_entranceRadialCoordinates hm hu hw hv
  have hs := hc.hasStrictFDerivAt' hd (by norm_num)
  refine ⟨hc.localInverse hd (by norm_num), ?_⟩
  exact ⟨hc.localInverse_apply_image hd (by norm_num), hc.to_localInverse hd (by norm_num),
    hs.to_localInverse.hasFDerivAt, hs.eventually_left_inverse, hs.eventually_right_inverse⟩

/-- Every point of the actual long entrance admits the C2 radial coordinate inverse. -/
theorem exists_entranceRegion_radial_inverse {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ∃ Ψ, EntranceRadialInverseAt y Ψ := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hchi, _, hPM⟩ := entranceRegion_stable_radial_bounds hk hy
  exact exists_entranceRadialInverseAt hm hu hw hv (by linarith [hchi.1]) (by linarith [hPM.1])

theorem EntranceRadialInverseAt.wall_coordinates {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) :
    ∀ᶠ z in 𝓝 (entranceRadialCoordinates y), Ψ z 1 = z 1 ∧ Ψ z 2 = z 2 ∧ Ψ z 3 = z 3 := by
  filter_upwards [H.right_inverse] with z hz
  exact ⟨by simpa [entranceRadialCoordinates] using congrArg (fun v : ProjectiveState => v 1) hz,
    by simpa [entranceRadialCoordinates] using congrArg (fun v : ProjectiveState => v 2) hz,
    by simpa [entranceRadialCoordinates] using congrArg (fun v : ProjectiveState => v 3) hz⟩

theorem EntranceRadialInverseAt.differential_apply {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) (v : ProjectiveState) :
    fderiv ℝ Ψ (entranceRadialCoordinates y) v =
      ![entranceStableRadius y / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 0 -
        entranceStablePartial y 1 / entranceStablePartial y 0 * v 1 -
        y 2 / ((entranceStablePhase y - 1) * entranceStablePartial y 0) * v 2 -
        entranceStablePartial y 3 / entranceStablePartial y 0 * v 3, v 1, v 2, v 3] := by
  rw [H.hasFDerivAt.fderiv, entranceRadialInverseDifferential_apply]

theorem EntranceRadialInverseAt.phase_partials {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) :
    let z := entranceRadialCoordinates y
    fderiv ℝ Ψ z (Pi.single 0 1) 0 = entranceStableRadius y /
        ((entranceStablePhase y - 1) * entranceStablePartial y 0) ∧
      fderiv ℝ Ψ z (Pi.single 1 1) 0 = -entranceStablePartial y 1 / entranceStablePartial y 0 ∧
      fderiv ℝ Ψ z (Pi.single 2 1) 0 = -y 2 /
        ((entranceStablePhase y - 1) * entranceStablePartial y 0) ∧
      fderiv ℝ Ψ z (Pi.single 3 1) 0 = -entranceStablePartial y 3 / entranceStablePartial y 0 := by
  simp [H.differential_apply, neg_div]

theorem EntranceRadialInverseAt.scalar_differential {y : ProjectiveState} {Ψ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) {f : ProjectiveState → ℝ} (hf : DifferentiableAt ℝ f y)
    (v : ProjectiveState) :
    fderiv ℝ (fun z => f (Ψ z)) (entranceRadialCoordinates y) v =
      fderiv ℝ f y (entranceRadialInverseDifferential y v) := by
  have hd : HasFDerivAt f (fderiv ℝ f y) (Ψ (entranceRadialCoordinates y)) := by
    rw [H.apply_base]
    exact hf.hasFDerivAt
  exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) (hd.comp _ H.hasFDerivAt).fderiv

theorem EntranceRadialInverseAt.unique {y : ProjectiveState} {Ψ Φ : ProjectiveState → ProjectiveState}
    (H : EntranceRadialInverseAt y Ψ) (J : EntranceRadialInverseAt y Φ) :
    Ψ =ᶠ[𝓝 (entranceRadialCoordinates y)] Φ := by
  have ht : Tendsto Φ (𝓝 (entranceRadialCoordinates y)) (𝓝 y) := by
    simpa only [J.apply_base] using J.contDiffAt.continuousAt.tendsto
  filter_upwards [J.right_inverse, ht.eventually H.left_inverse] with z hz hleft
  simpa only [hz] using hleft

end BianchiIX
