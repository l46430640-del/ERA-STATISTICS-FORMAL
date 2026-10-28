import BianchiIX.Measure.FourDimensionalNull
import BianchiIX.Dynamics.OrbitSaturation

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- A null three-dimensional source has a null full orbit saturation in every four-dimensional coordinate image. -/
theorem nullInFourCoordinates_orbitSaturation
    {C : (Fin 3 → ℝ) → NormalizedState} {Z : Set (Fin 3 → ℝ)}
    (hC : ∀ y ∈ Z, ContDiffAt ℝ 1 C y) (hZ : volume Z = 0) :
    NullInFourCoordinates (normalizedOrbitSaturation (C '' Z)) := by
  intro P hP
  let S : Set FourCoordinates := {p | Fin.tail p ∈ Z ∧
    p 0 ∈ normalizedMaxDomain (C (Fin.tail p)) 0}
  let F : FourCoordinates → NormalizedState := fun p => normalizedMaxCurve (C (Fin.tail p)) 0 (p 0)
  have hS : volume S = 0 := measure_mono_null (fun _ hp => hp.1) (volume_tail_preimage_null hZ)
  have hF (p : FourCoordinates) (hp : p ∈ S) : DifferentiableAt ℝ F p := by
    have htail : ContDiffAt ℝ 1 (fun q : FourCoordinates => Fin.tail q) p := by
      apply contDiffAt_pi.mpr
      intro i
      change ContDiffAt ℝ 1 (fun q : FourCoordinates => q i.succ) p
      fun_prop
    have htime : ContDiffAt ℝ 1 (fun q : FourCoordinates => q 0) p := by fun_prop
    have hpair := ((hC (Fin.tail p) hp.1).comp p htail).prodMk htime
    exact ((normalizedMaxCurve_regular hp.2).2.comp p hpair).differentiableAt (by norm_num)
  have hn : volume ((fun p => P (F p)) '' S) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun p hp => ((hP (F p)).comp p (hF p hp)).differentiableWithinAt) hS
  apply measure_mono_null _ hn
  rintro _ ⟨x, ⟨_, ⟨z, hz, rfl⟩, t, ht, rfl⟩, rfl⟩
  exact ⟨Fin.cons t z, by simpa [S] using And.intro hz ht, by simp [F]⟩

end BianchiIX
