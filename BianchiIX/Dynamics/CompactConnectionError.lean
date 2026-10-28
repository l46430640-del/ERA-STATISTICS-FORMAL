import BianchiIX.Dynamics.CompactConnectionCoordinates
import BianchiIX.Dynamics.EntranceRadialInverse

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def compactConnectionPhase (η : ℝ) (Y : CoreAngleState) : ℝ :=
  coreRadius (compactConnectionState η Y 0) (compactConnectionState η Y 2)

def compactConnectionError (η : ℝ) (Y : CoreAngleState) : ℝ :=
  compactConnectionPhase η Y - compactConnectionFinitePhase η Y

theorem compactConnectionError_chart_germ {η : ℝ} {Y : CoreAngleState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (compactConnectionEntry η Y) Ψ)
    (hentry : ContinuousAt (compactConnectionEntry η) Y)
    (hvalid : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z) :
    compactConnectionError η =ᶠ[𝓝 Y] (fun Z =>
      coreRadius (entranceReturnState (Ψ (compactConnectionCoordinates η Z)) 0)
        (entranceReturnState (Ψ (compactConnectionCoordinates η Z)) 2) - compactConnectionFinitePhase η Z) := by
  filter_upwards [hentry.tendsto.eventually HΨ.left_inverse, hvalid] with Z hz hv
  rw [compactConnectionCoordinates_eq hv, hz]
  rfl

/-- The error and its three input columns belong to the exact composed return, not a chosen surrogate. -/
theorem compactConnectionError_differential {η : ℝ} {Y : CoreAngleState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (compactConnectionEntry η Y) Ψ)
    (hentry : ContinuousAt (compactConnectionEntry η) Y)
    (hvalid : ∀ᶠ Z in 𝓝 Y, coreTailValid η Z)
    (hR : ContDiffAt ℝ 2 (compactConnectionFinitePhase η) Y)
    (hB : ∀ i : Fin 2, ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y)
    (hF : ContDiffAt ℝ 2 (fun z => coreRadius (entranceReturnState (Ψ z) 0)
      (entranceReturnState (Ψ z) 2)) (entranceRadialCoordinates (compactConnectionEntry η Y))) :
    ContDiffAt ℝ 2 (compactConnectionError η) Y ∧
      ∀ v : CoreAngleState,
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      let z := compactConnectionCoordinates η Y
      fderiv ℝ (compactConnectionError η) Y v =
        (fderiv ℝ F z (Pi.single 0 1) - 1) * fderiv ℝ (compactConnectionFinitePhase η) Y v +
        fderiv ℝ F z (Pi.single 1 1) *
          (v 1 * coreTailMultiplier η Y 0 + Y 1 * fderiv ℝ (fun Z => coreTailMultiplier η Z 0) Y v) +
        fderiv ℝ F z (Pi.single 2 1) *
          (v 2 * coreTailMultiplier η Y 1 + Y 2 * fderiv ℝ (fun Z => coreTailMultiplier η Z 1) Y v) := by
  let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
  let z := compactConnectionCoordinates η Y
  have hbase := compactConnectionCoordinates_eq hvalid.self_of_nhds
  have hF' : ContDiffAt ℝ 2 F z := by rw [show z = _ from hbase]; exact hF
  have hc := contDiffAt_compactConnectionCoordinates_two hR hB
  have heq := compactConnectionError_chart_germ HΨ hentry hvalid
  change compactConnectionError η =ᶠ[𝓝 Y] (F ∘ compactConnectionCoordinates η - compactConnectionFinitePhase η) at heq
  have hreg := (hF'.comp Y (g := F) (f := compactConnectionCoordinates η) hc).sub hR
  refine ⟨hreg.congr_of_eventuallyEq heq, ?_⟩
  intro v
  dsimp only
  have hdf := ((hF'.differentiableAt (by norm_num)).hasFDerivAt.comp Y
    ((hc.differentiableAt (by norm_num)).hasFDerivAt)).sub ((hR.differentiableAt (by norm_num)).hasFDerivAt)
  rw [heq.fderiv_eq, hdf.fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  rw [compactConnectionCoordinates_fderiv hR hB]
  have hlin (a b c : ℝ) : fderiv ℝ F z ![a, b, c, 0] =
      a * fderiv ℝ F z (Pi.single 0 1) + b * fderiv ℝ F z (Pi.single 1 1) +
        c * fderiv ℝ F z (Pi.single 2 1) := by
    have H : (![a, b, c, 0] : ProjectiveState) =
        a • Pi.single 0 1 + b • Pi.single 1 1 + c • Pi.single 2 1 := by
      ext i
      fin_cases i <;> simp
    rw [H, map_add, map_add, map_smul, map_smul, map_smul]
    rfl
  rw [hlin]
  ring

end BianchiIX
