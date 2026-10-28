import BianchiIX.Dynamics.PartialCoreBoundaryResponse
import BianchiIX.Dynamics.PartialCoreDownwardMultipliers
import BianchiIX.Dynamics.ReferenceIncomingReturn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Formula (E.24), including the incoming section, for the same ordinary first downward return. -/
theorem partialCoreDownwardReturn_reference_response {k z : ℝ} (hk : 6 ≤ k)
    (hz : z ∈ Ico (-Real.arcosh k) (Real.arcosh k)) :
    let y := referencePulse k (z / k)
    let τ := partialCoreDownwardReturnTime
    0 < τ y ∧ ContDiffAt ℝ 2 τ y ∧
      (∀ᶠ x in 𝓝 y,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState x) 0 ∧
          projectiveOriginalFlow x 0 t 2 = 1 ∧
          normalizedEventRate projectiveActiveWall (fromProjectiveState x) 0 t < 0} (τ x) ∧
        projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
        projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1) ∧
      (∀ i : Fin 2, 0 < partialCoreReturnMultiplier τ y i ∧
        ContDiffAt ℝ 1 (fun x => Real.log (partialCoreReturnMultiplier τ x i)) y ∧
        ContDiffAt ℝ 1 (fun x => partialCoreReturnMultiplier τ x i) y) ∧
      partialCoreReturnMultiplier τ y 0 =
        (k / Real.cosh z) * Real.exp (-(k / 2) * (Real.arcosh k - z)) ∧
      partialCoreReturnMultiplier τ y 1 = Real.exp (-2 * (Real.arcosh k - z) / k) ∧
      HasDerivAt (fun u : ℝ =>
        let x := fromCoreAngleState z ![k, u, 0]
        let b := projectiveOriginalFlow x 0 (τ x)
        coreRadius (b 0) (b 2) - k)
        (-2 / Real.cosh z * (1 - Real.exp (-(k / 2) * (Real.arcosh k - z)))) 0 ∧
      HasDerivAt (fun a => Real.log (partialCoreReturnMultiplier τ (referencePulse k (a / k)) 0))
        (k / 2 - Real.tanh z) z ∧
      HasDerivAt (fun a => Real.log (partialCoreReturnMultiplier τ (referencePulse k (a / k)) 1))
        (2 / k) z := by
  intro y τ
  have hk0 : 0 < k := by linarith only [hk]
  have hk1 : 1 < k := by linarith only [hk]
  have hs : z / k ∈ Ico (-referenceHalfTime k) (referenceHalfTime k) := by
    constructor
    · simpa only [referenceHalfTime, neg_div] using div_le_div_of_nonneg_right hz.1 hk0.le
    · exact div_lt_div_of_pos_right hz.2 hk0
  obtain ⟨hy, hV⟩ := referencePulse_incoming_core_data hk hs
  have hR : coreRadius (y 0) (y 2) = k := referencePulse_radius hk0.le _
  have hD : 0 < projectiveStateDenom y := referencePulse_denom_pos k _
  have hc := fromProjectiveState_constraint hD.ne'
  have HR := partialCoreDownwardReturn_regular hk hy hR hV
  have HB := partialCoreDownwardReturn_bounds hk hy hR hV
  have HM := partialCoreDownwardReturn_multiplier_response hk hy hR hV
  have hpos : 0 < τ y := HR.1.1.1
  have hcτ : ContDiffAt ℝ 2 τ y := HR.2.1
  have hfirst : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1} (τ y) :=
    ⟨⟨hpos, normalizedMaxDomain_contains_Ici_of_constraint hc 0 hpos.le, HR.1.1.2⟩,
      fun _ ht => HR.1.2 ⟨ht.1, ht.2.2⟩⟩
  have href := referencePulse_incoming_firstReturn hk1 hs
  have htime : τ y = referenceShiftClock k (z / k) (referenceHalfTime k) :=
    hfirst.unique href.2.1
  have hnear : ∀ᶠ x in 𝓝 y,
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState x) 0 ∧
        projectiveOriginalFlow x 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState x) 0 t < 0} (τ x) ∧
      projectiveOriginalFlow x 0 (τ x) 1 = x 1 * partialCoreReturnMultiplier τ x 0 ∧
      projectiveOriginalFlow x 0 (τ x) 3 = (x 2 * x 3) * partialCoreReturnMultiplier τ x 1 := by
    filter_upwards [HR.2.2.2.1, HM.1] with x hx hm
    exact ⟨hx.1, hm⟩
  refine ⟨hpos, hcτ, hnear, HM.2.1, ?_⟩
  exact partialCore_boundary_response_of_return hk τ hcτ hpos htime
    (hnear.mono fun _ h => ⟨h.1.1.2.2.1, h.2⟩) HM.2.1
    (fun t ht => ⟨(HB.2.2 t ht).1, (HB.2.2 t ht).2.1⟩)
    (partialCoreDownwardReturn_variation hk hy hR hV)

end BianchiIX
