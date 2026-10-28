import BianchiIX.Dynamics.ReferenceEntranceHeightResponse
import BianchiIX.Dynamics.ReferenceEntranceMixedResponse

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

theorem EntranceRadialInverseAt.referenceEntrance_height_column_germ {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    (fun w => fderiv ℝ (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
      ![k, 0, w, 0] (Pi.single 1 1)) =ᶠ[𝓝 v] referenceEntranceStrongResponse k := by
  have hyc : Continuous (referenceEntranceState k) := by
    unfold referenceEntranceState
    fun_prop
  have hzc : Continuous (fun w : ℝ => (![k, 0, w, 0] : ProjectiveState)) := by fun_prop
  have hz : Tendsto (fun w : ℝ => (![k, 0, w, 0] : ProjectiveState)) (𝓝 v)
      (𝓝 (entranceRadialCoordinates (referenceEntranceState k v))) := by
    rw [referenceEntrance_radialCoordinates hk hv]
    exact hzc.continuousAt.tendsto
  have hleft : (fun y => Ψ (entranceRadialCoordinates y)) =ᶠ[𝓝 (referenceEntranceState k v)] id := HΨ.left_inverse
  filter_upwards [eventually_gt_nhds hv.1, eventually_lt_nhds hv.2,
    hyc.continuousAt.tendsto.eventually hleft.eventuallyEq_nhds,
    hz.eventually (HΨ.contDiffAt.eventually (by norm_num))] with w hw0 hw1 hleft' hΨ'
  exact referenceEntrance_strong_column_of_left_inverse hk ⟨hw0, hw1⟩
    (hΨ'.differentiableAt (by norm_num)) hleft'

theorem EntranceRadialInverseAt.referenceEntrance_height_mixed_derivative {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    HasDerivAt (fun w => fderiv ℝ
      (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
      ![k, 0, w, 0] (Pi.single 1 1)) (referenceEntranceHeightResponse k v) v := by
  exact (hasDerivAt_referenceEntranceStrongResponse_height (show 1 < k by linarith) hv)
    |>.congr_of_eventuallyEq (HΨ.referenceEntrance_height_column_germ hk hv)

/-- The mixed response has a nonzero limit as the waiting interval shrinks to zero. -/
theorem tendsto_referenceEntrance_height_mixed_derivative {k : ℝ} (hk : 7 / 4 ≤ k)
    (Ψ : ℝ → ProjectiveState → ProjectiveState)
    (HΨ : ∀ v : ℝ, (0 < v ∧ v < 1) → EntranceRadialInverseAt (referenceEntranceState k v) (Ψ v)) :
    Tendsto (fun v => deriv (fun w => fderiv ℝ
      (fun z => coreRadius (entranceReturnState (Ψ v z) 0) (entranceReturnState (Ψ v z) 2))
      ![k, 0, w, 0] (Pi.single 1 1)) v) (𝓝[<] 1) (𝓝 (k / Real.sqrt (k ^ 2 - 1))) := by
  apply (tendsto_referenceEntranceHeightResponse_one (show 1 < k by linarith)).congr'
  filter_upwards [(eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with v hv0 hv1
  exact ((HΨ v ⟨hv0, hv1⟩).referenceEntrance_height_mixed_derivative hk ⟨hv0, hv1⟩).deriv.symm

theorem exists_referenceEntrance_height_mixed_limit {k : ℝ} (hk : 7 / 4 ≤ k) :
    ∃ Ψ : ℝ → ProjectiveState → ProjectiveState,
      (∀ v : ℝ, (0 < v ∧ v < 1) → EntranceRadialInverseAt (referenceEntranceState k v) (Ψ v)) ∧
      Tendsto (fun v => deriv (fun w => fderiv ℝ
        (fun z => coreRadius (entranceReturnState (Ψ v z) 0) (entranceReturnState (Ψ v z) 2))
        ![k, 0, w, 0] (Pi.single 1 1)) v) (𝓝[<] 1) (𝓝 (k / Real.sqrt (k ^ 2 - 1))) := by
  have hex : ∀ v : ℝ, ∃ Ψ : ProjectiveState → ProjectiveState,
      (0 < v ∧ v < 1) → EntranceRadialInverseAt (referenceEntranceState k v) Ψ := by
    intro v
    by_cases hv : 0 < v ∧ v < 1
    · obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk (referenceEntrance_region hk hv) hv.1
      exact ⟨Ψ, fun _ => HΨ⟩
    · exact ⟨id, fun h => (hv h).elim⟩
  choose Ψ HΨ using hex
  exact ⟨Ψ, HΨ, tendsto_referenceEntrance_height_mixed_derivative hk Ψ HΨ⟩

/-- At any sufficiently large radius, the mixed response exceeds a proposed inverse-radius bound. -/
theorem exists_referenceEntrance_height_mixed_gt {C k : ℝ} (hk : 2 ≤ k) (hC : C < k) :
    ∃ v : ℝ, (0 < v ∧ v < 1) ∧ ∀ Ψ : ProjectiveState → ProjectiveState,
      EntranceRadialInverseAt (referenceEntranceState k v) Ψ →
      C / k < deriv (fun w => fderiv ℝ
        (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
        ![k, 0, w, 0] (Pi.single 1 1)) v := by
  have hk0 : 0 < k := by linarith
  have hs0 : 0 < Real.sqrt (k ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith only [hk])
  have hL : 1 < k / Real.sqrt (k ^ 2 - 1) :=
    (one_lt_div hs0).mpr ((Real.sqrt_lt' hk0).mpr (by linarith))
  have hCL : C / k < k / Real.sqrt (k ^ 2 - 1) := ((div_lt_one hk0).mpr hC).trans hL
  have hlarge := (tendsto_referenceEntranceHeightResponse_one (show 1 < k by linarith)).eventually
    (eventually_gt_nhds hCL)
  have hpos : ∀ᶠ v : ℝ in 𝓝[<] 1, 0 < v :=
    (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ v : ℝ in 𝓝[<] 1, v < 1 := self_mem_nhdsWithin
  obtain ⟨v, hv0, hv1, Hv⟩ := (hpos.and (hlt.and hlarge)).exists
  refine ⟨v, ⟨hv0, hv1⟩, ?_⟩
  intro Ψ HΨ
  rw [(HΨ.referenceEntrance_height_mixed_derivative (by linarith) ⟨hv0, hv1⟩).deriv]
  exact Hv

theorem not_uniform_referenceEntrance_height_mixed_bound :
    ¬ ∃ C : ℝ, ∀ k : ℝ, 2 ≤ k → ∀ v : ℝ, (0 < v ∧ v < 1) →
      ∀ Ψ : ProjectiveState → ProjectiveState,
      EntranceRadialInverseAt (referenceEntranceState k v) Ψ →
      |deriv (fun w => fderiv ℝ
        (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
        ![k, 0, w, 0] (Pi.single 1 1)) v| ≤ C / k := by
  rintro ⟨C, HC⟩
  let k := max 2 C + 1
  have hk : 2 ≤ k := by dsimp [k]; linarith [le_max_left (2 : ℝ) C]
  have hC : C < k := by dsimp [k]; linarith [le_max_right (2 : ℝ) C]
  obtain ⟨v, hv, Hv⟩ := exists_referenceEntrance_height_mixed_gt hk hC
  have hk' : 7 / 4 ≤ k := by linarith
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk' (referenceEntrance_region hk' hv) hv.1
  exact not_lt_of_ge ((le_abs_self _).trans (HC k hk v hv Ψ HΨ)) (Hv Ψ HΨ)

end BianchiIX
