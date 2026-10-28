import BianchiIX.Dynamics.ReferenceEntranceHeightMixed
import BianchiIX.Dynamics.EntrancePhysicalBounds
import BianchiIX.Analysis.HessianEvaluation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem hasDerivAt_referenceEntrance_strong_line (k v u : ℝ) :
    HasDerivAt (fun a : ℝ => (![k, a, v, 0] : ProjectiveState)) (Pi.single 1 1) u := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using hasDerivAt_const u k
  · change HasDerivAt (fun a : ℝ => a) 1 u
    exact hasDerivAt_id' u
  · simpa using hasDerivAt_const u v
  · simpa using hasDerivAt_const u (0 : ℝ)

theorem hasDerivAt_referenceEntrance_height_line (k v : ℝ) :
    HasDerivAt (fun a : ℝ => (![k, 0, a, 0] : ProjectiveState)) (Pi.single 2 1) v := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa using hasDerivAt_const v k
  · simpa using hasDerivAt_const v (0 : ℝ)
  · change HasDerivAt (fun a : ℝ => a) 1 v
    exact hasDerivAt_id' v
  · simpa using hasDerivAt_const v (0 : ℝ)

theorem EntranceRadialInverseAt.referenceEntrance_return_regular {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    ContDiffAt ℝ 2 (fun z => coreRadius (entranceReturnState (Ψ z) 0)
      (entranceReturnState (Ψ z) 2)) ![k, 0, v, 0] := by
  have hy := referenceEntrance_region hk hv
  have hR := referenceEntrance_radius (show 0 < k by linarith) ⟨hv.1, by linarith [hv.2]⟩
  have H := HΨ.physical_return_regular (by rw [hR]; exact hk) hy.1 hy.2.2.1 hv hy.2.2.2.2
  simpa only [referenceEntrance_radialCoordinates hk hv] using H

theorem EntranceRadialInverseAt.referenceEntrance_height_value_germ {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    (fun a : ℝ => coreRadius (entranceReturnState (Ψ ![k, 0, a, 0]) 0)
      (entranceReturnState (Ψ ![k, 0, a, 0]) 2)) =ᶠ[𝓝 v] (fun _ => k) := by
  have hc : Continuous (referenceEntranceState k) := by unfold referenceEntranceState; fun_prop
  filter_upwards [eventually_gt_nhds hv.1, eventually_lt_nhds hv.2,
    hc.continuousAt.tendsto.eventually HΨ.left_inverse] with a ha0 ha1 hleft
  change Ψ (entranceRadialCoordinates (referenceEntranceState k a)) = referenceEntranceState k a at hleft
  rw [referenceEntrance_radialCoordinates hk ⟨ha0, ha1⟩] at hleft
  rw [hleft, (referenceEntrance_return hk ⟨ha0, ha1⟩).2,
    referencePulse_radius (show 0 ≤ k by linarith)]

theorem EntranceRadialInverseAt.referenceEntrance_active_zero {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    fderiv ℝ (fun z => coreRadius (entranceReturnState (Ψ z) 0)
      (entranceReturnState (Ψ z) 2)) ![k, 0, v, 0] (Pi.single 2 1) = 0 := by
  have hF := (HΨ.referenceEntrance_return_regular hk hv).differentiableAt (by norm_num)
  have H := hF.hasFDerivAt.comp_hasDerivAt v (hasDerivAt_referenceEntrance_height_line k v)
  have H0 := (hasDerivAt_const v k).congr_of_eventuallyEq (HΨ.referenceEntrance_height_value_germ hk hv)
  exact H.unique H0

/-- Symmetry of the actual C2 return turns the known height derivative into a strong-amplitude derivative. -/
theorem EntranceRadialInverseAt.referenceEntrance_active_strong_derivative {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    HasDerivAt (fun u : ℝ => fderiv ℝ
      (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
      ![k, u, v, 0] (Pi.single 2 1)) (referenceEntranceHeightResponse k v) 0 := by
  let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
  let z : ProjectiveState := ![k, 0, v, 0]
  have hF : ContDiffAt ℝ 2 F z := HΨ.referenceEntrance_return_regular hk hv
  have hdf : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hU := hasDerivAt_fderiv_apply_const hdf (hasDerivAt_referenceEntrance_strong_line k v 0) (Pi.single 2 1)
  have hV := hasDerivAt_fderiv_apply_const hdf (hasDerivAt_referenceEntrance_height_line k v) (Pi.single 1 1)
  have he := hV.unique (HΨ.referenceEntrance_height_mixed_derivative hk hv)
  have hs := (hF.isSymmSndFDerivAt (by norm_num)).eq (Pi.single 1 1) (Pi.single 2 1)
  exact hU.congr_deriv (hs.trans he)

theorem EntranceRadialInverseAt.referenceEntrance_active_slope {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    Tendsto (fun u : ℝ => fderiv ℝ
      (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
      ![k, u, v, 0] (Pi.single 2 1) / u) (𝓝[>] 0) (𝓝 (referenceEntranceHeightResponse k v)) := by
  have H := (HΨ.referenceEntrance_active_strong_derivative hk hv).tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
  convert! H using 1
  ext u
  rw [slope_def_field, HΨ.referenceEntrance_active_zero hk hv, sub_zero, sub_zero]

end BianchiIX
