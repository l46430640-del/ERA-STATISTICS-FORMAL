import BianchiIX.Dynamics.ReferenceEntranceAsymptotic

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

theorem referenceEntrance_region {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    entranceRegion k (referenceEntranceState k v) := by
  have hR := referenceEntrance_radius (show 0 < k by linarith) ⟨hv.1, by linarith [hv.2]⟩
  exact ⟨le_add_of_nonneg_right (Real.sqrt_nonneg _),
    by rw [hR, sub_self, abs_zero]; linarith,
    by dsimp [referenceEntranceState]; norm_num,
    ⟨hv.1.le, hv.2.le⟩, by dsimp [referenceEntranceState]; norm_num⟩

/-- A local left inverse already determines the strong column on the reference axis. -/
theorem referenceEntrance_strong_column_of_left_inverse {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) {Ψ : ProjectiveState → ProjectiveState}
    (hΨ : DifferentiableAt ℝ Ψ ![k, 0, v, 0])
    (hleft : (fun y => Ψ (entranceRadialCoordinates y)) =ᶠ[𝓝 (referenceEntranceState k v)] id) :
    fderiv ℝ (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
      ![k, 0, v, 0] (Pi.single 1 1) = referenceEntranceStrongResponse k v := by
  let y := referenceEntranceState k v
  let z : ProjectiveState := ![k, 0, v, 0]
  let F := fun y : ProjectiveState => coreRadius (entranceReturnState y 0) (entranceReturnState y 2)
  have hy : entranceRegion k y := referenceEntrance_region hk hv
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hcoord : entranceRadialCoordinates y = z := referenceEntrance_radialCoordinates hk hv
  have hbase : Ψ z = y := by
    have hb : Ψ (entranceRadialCoordinates y) = y := hleft.self_of_nhds
    rw [hcoord] at hb
    exact hb
  have hInv : entranceRadialInverseDifferential y (Pi.single 1 1) = Pi.single 1 1 :=
    entranceRadialInverseDifferential_strong_zero (v := v) hm
  have hdir : entranceRadialDifferential y (Pi.single 1 1) = Pi.single 1 1 := by
    have H := (entranceRegion_radialDifferential_inverse hk hy hv.1).2 (Pi.single 1 1)
    rw [hInv] at H
    exact H
  have hρ := hasFDerivAt_entranceRadialCoordinates hm
    (by change |(0 : ℝ)| < 1 / 200; norm_num) (by change |(0 : ℝ)| < 1 / 200; norm_num) hv.1
  have hΨ' : HasFDerivAt Ψ (fderiv ℝ Ψ z) (entranceRadialCoordinates y) := by rw [hcoord]; exact hΨ.hasFDerivAt
  have hcomp := hΨ'.comp y hρ
  have hid : HasFDerivAt (fun q => Ψ (entranceRadialCoordinates q))
      (ContinuousLinearMap.id ℝ ProjectiveState) y :=
    (hasFDerivAt_id y).congr_of_eventuallyEq hleft
  have hlin := congrArg (fun L : ProjectiveState →L[ℝ] ProjectiveState => L (Pi.single 1 1)) (hcomp.unique hid)
  have hdΨ : fderiv ℝ Ψ z (Pi.single 1 1) = Pi.single 1 1 := by
    simpa only [ContinuousLinearMap.comp_apply, hdir, ContinuousLinearMap.id_apply] using hlin
  have hR := referenceEntrance_radius (show 0 < k by linarith) ⟨hv.1, by linarith [hv.2]⟩
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by rw [hR]; exact hk
  have hret := entranceReturn_regular hk' hy.1 hy.2.2.1 hv hy.2.2.2.2
  have hV : 0 < entranceReturnState y 2 := by
    rw [(entranceReturn_active_component hk' hy.1 hy.2.2.1 hv hy.2.2.2.2).1]
    norm_num
  have hF : DifferentiableAt ℝ F y := (hasFDerivAt_coreRadius_state hV).differentiableAt.comp y
    (hret.2.2.1.differentiableAt (by norm_num))
  have hF' : HasFDerivAt F (fderiv ℝ F y) (Ψ z) := by rw [hbase]; exact hF.hasFDerivAt
  have H := hF'.comp z hΨ.hasFDerivAt
  simp only [Function.comp_def] at H
  rw [H.fderiv, ContinuousLinearMap.comp_apply, hdΨ]
  exact referenceEntrance_physical_strong_derivative hk hv

theorem EntranceRadialInverseAt.referenceEntrance_strong_column_germ {k v : ℝ}
    (hk : 7 / 4 < k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    (fun r => fderiv ℝ (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
      ![r, 0, v, 0] (Pi.single 1 1)) =ᶠ[𝓝 k] (fun r => referenceEntranceStrongResponse r v) := by
  have hyc : Continuous (fun r => referenceEntranceState r v) := by
    unfold referenceEntranceState
    fun_prop
  have hzc : Continuous (fun r : ℝ => (![r, 0, v, 0] : ProjectiveState)) := by fun_prop
  have hz : Tendsto (fun r : ℝ => (![r, 0, v, 0] : ProjectiveState)) (𝓝 k)
      (𝓝 (entranceRadialCoordinates (referenceEntranceState k v))) := by
    rw [referenceEntrance_radialCoordinates hk.le hv]
    exact hzc.continuousAt.tendsto
  have hleft : (fun y => Ψ (entranceRadialCoordinates y)) =ᶠ[𝓝 (referenceEntranceState k v)] id := HΨ.left_inverse
  filter_upwards [eventually_gt_nhds hk, hyc.continuousAt.tendsto.eventually hleft.eventuallyEq_nhds,
    hz.eventually (HΨ.contDiffAt.eventually (by norm_num))] with r hr hleft' hΨ'
  exact referenceEntrance_strong_column_of_left_inverse hr.le hv (hΨ'.differentiableAt (by norm_num)) hleft'

theorem EntranceRadialInverseAt.referenceEntrance_mixed_derivative {k v : ℝ}
    (hk : 7 / 4 < k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    HasDerivAt (fun r => fderiv ℝ
      (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
      ![r, 0, v, 0] (Pi.single 1 1))
      (deriv (fun r => referenceEntranceStrongResponse r v) k) k := by
  exact (hasDerivAt_referenceEntranceStrongResponse (show 1 < k by linarith) hv).differentiableAt.hasDerivAt
    |>.congr_of_eventuallyEq (HΨ.referenceEntrance_strong_column_germ hk hv)

/-- The limit is independent of the chosen local radial inverse at each reference point. -/
theorem tendsto_referenceEntrance_mixed_derivative {v : ℝ} (hv : 0 < v ∧ v < 1)
    (Ψ : ℝ → ProjectiveState → ProjectiveState)
    (HΨ : ∀ k : ℝ, 2 ≤ k → EntranceRadialInverseAt (referenceEntranceState k v) (Ψ k)) :
    Tendsto (fun k : ℝ => k ^ 2 / v * deriv (fun r => fderiv ℝ
      (fun z => coreRadius (entranceReturnState (Ψ k z) 0) (entranceReturnState (Ψ k z) 2))
      ![r, 0, v, 0] (Pi.single 1 1)) k) atTop (𝓝 2) := by
  apply (tendsto_referenceEntranceStrongResponse_scaled_derivative hv).congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with k hk
  rw [((HΨ k hk).referenceEntrance_mixed_derivative (by linarith) hv).deriv]

theorem exists_referenceEntrance_mixed_asymptotic {v : ℝ} (hv : 0 < v ∧ v < 1) :
    ∃ Ψ : ℝ → ProjectiveState → ProjectiveState,
      (∀ k : ℝ, 2 ≤ k → EntranceRadialInverseAt (referenceEntranceState k v) (Ψ k)) ∧
      Tendsto (fun k : ℝ => k ^ 2 / v * deriv (fun r => fderiv ℝ
        (fun z => coreRadius (entranceReturnState (Ψ k z) 0) (entranceReturnState (Ψ k z) 2))
        ![r, 0, v, 0] (Pi.single 1 1)) k) atTop (𝓝 2) := by
  have hex : ∀ k : ℝ, ∃ Ψ : ProjectiveState → ProjectiveState,
      2 ≤ k → EntranceRadialInverseAt (referenceEntranceState k v) Ψ := by
    intro k
    by_cases hk : 2 ≤ k
    · obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse (show 7 / 4 ≤ k by linarith)
        (referenceEntrance_region (show 7 / 4 ≤ k by linarith) hv) hv.1
      exact ⟨Ψ, fun _ => HΨ⟩
    · exact ⟨id, fun h => (hk h).elim⟩
  choose Ψ HΨ using hex
  exact ⟨Ψ, HΨ, tendsto_referenceEntrance_mixed_derivative hv Ψ HΨ⟩

end BianchiIX
