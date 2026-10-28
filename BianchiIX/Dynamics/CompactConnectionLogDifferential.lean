import BianchiIX.Dynamics.CompactConnectionCoordinates
import BianchiIX.Dynamics.EntranceRadialInverse
import BianchiIX.Dynamics.EntranceActualWallResponse

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def compactConnectionLogWalls (η : ℝ) (Y : CoreAngleState) : Fin 2 → ℝ :=
  entranceLogWalls 1 (compactConnectionState η Y)

theorem compactConnectionLogWalls_chart_germ {η : ℝ} {Y : CoreAngleState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (compactConnectionEntry η Y) Ψ)
    (hentry : ContinuousAt (compactConnectionEntry η) Y)
    (hvalid : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z) :
    compactConnectionLogWalls η =ᶠ[𝓝 Y] (fun Z =>
      entranceLogWalls 1 (entranceReturnState (Ψ (compactConnectionCoordinates η Z)))) := by
  filter_upwards [hentry.tendsto.eventually HΨ.left_inverse, hvalid] with Z hz hv
  rw [compactConnectionCoordinates_eq hv, hz]
  rfl

/-- The logarithmic derivative is pulled back through the same actual finite passage. -/
theorem compactConnectionLogWalls_differential {η : ℝ} {Y : CoreAngleState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (compactConnectionEntry η Y) Ψ)
    (hentry : ContinuousAt (compactConnectionEntry η) Y)
    (hvalid : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z)
    (hc : DifferentiableAt ℝ (compactConnectionCoordinates η) Y)
    (hL : DifferentiableAt ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
      (entranceRadialCoordinates (compactConnectionEntry η Y))) :
    DifferentiableAt ℝ (compactConnectionLogWalls η) Y ∧ ∀ v : CoreAngleState,
      fderiv ℝ (compactConnectionLogWalls η) Y v =
        fderiv ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
          (compactConnectionCoordinates η Y) (fderiv ℝ (compactConnectionCoordinates η) Y v) := by
  have heq := compactConnectionLogWalls_chart_germ HΨ hentry hvalid
  have hbase := compactConnectionCoordinates_eq hvalid.self_of_nhds
  have hL' : DifferentiableAt ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
      (compactConnectionCoordinates η Y) := by rw [hbase]; exact hL
  have hd := hL'.hasFDerivAt.comp Y hc.hasFDerivAt
  refine ⟨hd.differentiableAt.congr_of_eventuallyEq heq, ?_⟩
  intro v
  rw [heq.fderiv_eq]
  exact congrArg (fun L : CoreAngleState →L[ℝ] (Fin 2 → ℝ) => L v) hd.fderiv

theorem compactConnectionLogWalls_fderiv {η : ℝ} {Y : CoreAngleState}
    (hstate : DifferentiableAt ℝ (compactConnectionState η) Y)
    (hu : compactConnectionState η Y 1 ≠ 0) (hw : compactConnectionState η Y 3 ≠ 0)
    (v : CoreAngleState) :
    fderiv ℝ (compactConnectionLogWalls η) Y v =
      ![fderiv ℝ (compactConnectionState η) Y v 1 / compactConnectionState η Y 1,
        fderiv ℝ (compactConnectionState η) Y v 3 / compactConnectionState η Y 3] := by
  have hd := (hasFDerivAt_entranceLogWalls 1 hu hw).differentiableAt.hasFDerivAt.comp Y hstate.hasFDerivAt
  change fderiv ℝ (entranceLogWalls 1 ∘ compactConnectionState η) Y v = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply, entranceLogWalls_fderiv_apply 1 hu hw]
  simp only [entranceWallTangent, one_pow, one_mul]

end BianchiIX
