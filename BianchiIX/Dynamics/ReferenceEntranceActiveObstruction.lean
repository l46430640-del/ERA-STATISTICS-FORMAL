import BianchiIX.Dynamics.ReferenceEntranceActiveBoundary

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem EntranceRadialInverseAt.referenceEntrance_active_exceeds_boundary_envelope {C k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) (hC : C / k < referenceEntranceHeightResponse k v)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    ∀ᶠ u : ℝ in 𝓝[>] 0,
      C * (u + v * u ^ 2) / k < fderiv ℝ
        (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
        ![k, u, v, 0] (Pi.single 2 1) := by
  have hp : Tendsto (fun u : ℝ => C * (1 + v * u) / k) (𝓝[>] 0) (𝓝 (C / k)) := by
    simpa only [mul_zero, add_zero, mul_one] using
      (by fun_prop : Continuous (fun u : ℝ => C * (1 + v * u) / k)).continuousAt (x := 0) |>.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have H := ((HΨ.referenceEntrance_active_slope hk hv).sub hp).eventually
    (eventually_gt_nhds (sub_pos.mpr hC))
  filter_upwards [H, self_mem_nhdsWithin] with u hu hu0
  have hu' : 0 < u := hu0
  have HH := (lt_div_iff₀ hu').mp (sub_pos.mp hu)
  convert! HH using 1
  ring

/-- Strict boundary violations persist at positive weak amplitude inside the actual return domain. -/
theorem EntranceRadialInverseAt.exists_referenceEntrance_positive_active_violation {C k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) (hC : C / k < referenceEntranceHeightResponse k v)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u ∈ Ioo (0 : ℝ) δ, ∃ w ∈ Ioo (0 : ℝ) δ,
      entranceReturnValid (Ψ ![k, u, v, w]) ∧ 0 < projectiveStateDenom (Ψ ![k, u, v, w]) ∧
      entranceRadialCoordinates (Ψ ![k, u, v, w]) = ![k, u, v, w] ∧
      ContDiffAt ℝ 2 (fun z => coreRadius (entranceReturnState (Ψ z) 0)
        (entranceReturnState (Ψ z) 2)) ![k, u, v, w] ∧
      C * (u + v * (u + w) ^ 2) / k < |fderiv ℝ
        (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
        ![k, u, v, w] (Pi.single 2 1)| := by
  let y := referenceEntranceState k v
  let z : ProjectiveState := ![k, 0, v, 0]
  let c := fun p : ℝ × ℝ => (![k, p.1, v, p.2] : ProjectiveState)
  let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
  let P := fun p : ℝ × ℝ => entranceReturnValid (Ψ (c p)) ∧
    0 < projectiveStateDenom (Ψ (c p)) ∧ entranceRadialCoordinates (Ψ (c p)) = c p ∧
    ContDiffAt ℝ 2 F (c p)
  have hcoord : entranceRadialCoordinates y = z := referenceEntrance_radialCoordinates hk hv
  have hΨ : Tendsto Ψ (𝓝 z) (𝓝 y) := by
    rw [← hcoord]
    simpa only [HΨ.apply_base] using HΨ.contDiffAt.continuousAt.tendsto
  have hc : Tendsto c (𝓝 (0, 0)) (𝓝 z) := (by fun_prop : Continuous c).continuousAt.tendsto
  have hp := hΨ.comp hc
  have hy := referenceEntrance_region hk hv
  have hR := referenceEntrance_radius (show 0 < k by linarith) ⟨hv.1, by linarith [hv.2]⟩
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by rw [hR]; exact hk
  have H := entranceReturn_regular hk' hy.1 hy.2.2.1 hv hy.2.2.2.2
  have hD := entrance_initial_denom_pos hk' hy.1 hy.2.2.1 hv hy.2.2.2.2
  have hright : ∀ᶠ q in 𝓝 z, entranceRadialCoordinates (Ψ q) = q := by
    rw [← hcoord]
    exact HΨ.right_inverse
  have hF : ContDiffAt ℝ 2 F z := HΨ.referenceEntrance_return_regular hk hv
  have hcommon : ∀ᶠ p in 𝓝 ((0, 0) : ℝ × ℝ), P p := by
    filter_upwards [hp.eventually H.2.2.2.2.2,
      hp.eventually (continuous_projectiveStateDenom.continuousAt.eventually (eventually_gt_nhds hD)),
      hc.eventually hright, hc.eventually (hF.eventually (by norm_num))] with p hvp hDp hrp hFp
    exact ⟨hvp, hDp, hrp, hFp⟩
  have hnear : ∀ᶠ u : ℝ in 𝓝 0, ∀ᶠ p in 𝓝 (u, 0), P p :=
    (by fun_prop : Continuous (fun u : ℝ => (u, (0 : ℝ)))).continuousAt.tendsto.eventually hcommon.eventually_nhds
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := self_mem_nhdsWithin
  have hsmall : ∀ᶠ u : ℝ in 𝓝[>] 0, u < δ := (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  obtain ⟨u, hu0, huδ, hviol, hloc⟩ :=
    (hpos.and (hsmall.and ((HΨ.referenceEntrance_active_exceeds_boundary_envelope hk hv hC).and
      (hnear.filter_mono nhdsWithin_le_nhds)))).exists
  have hreg : ContDiffAt ℝ 2 F (c (u, 0)) := hloc.self_of_nhds.2.2.2
  have hcol : ContinuousAt (fun q => fderiv ℝ F q (Pi.single 2 1)) (c (u, 0)) :=
    (hreg.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have hpath : ContinuousAt (fun w : ℝ => c (u, w)) 0 := by fun_prop
  have hcolW : ContinuousAt (fun w : ℝ => fderiv ℝ F (c (u, w)) (Pi.single 2 1)) 0 :=
    ContinuousAt.comp (g := fun q => fderiv ℝ F q (Pi.single 2 1))
      (f := fun w : ℝ => c (u, w)) (x := 0) hcol hpath
  have hgap : ContinuousAt (fun w : ℝ =>
      fderiv ℝ F (c (u, w)) (Pi.single 2 1) - C * (u + v * (u + w) ^ 2) / k) 0 :=
    hcolW.sub (by fun_prop)
  have hgap0 : 0 < fderiv ℝ F (c (u, 0)) (Pi.single 2 1) - C * (u + v * (u + 0) ^ 2) / k := by
    simpa only [add_zero] using sub_pos.mpr hviol
  have hgood : ∀ᶠ w : ℝ in 𝓝 0, P (u, w) :=
    (by fun_prop : Continuous (fun w : ℝ => (u, w))).continuousAt.tendsto.eventually hloc
  obtain ⟨w, hw0, hwδ, hPw, hgw⟩ := (hpos.and (hsmall.and
    ((hgood.filter_mono nhdsWithin_le_nhds).and
      ((hgap.eventually (eventually_gt_nhds hgap0)).filter_mono nhdsWithin_le_nhds)))).exists
  refine ⟨u, ⟨hu0, huδ⟩, w, ⟨hw0, hwδ⟩, hPw.1, hPw.2.1, hPw.2.2.1, hPw.2.2.2, ?_⟩
  exact (sub_pos.mp hgw).trans_le (le_abs_self _)

theorem exists_referenceEntrance_active_envelope_violation {C k v₀ : ℝ}
    (hk : 2 ≤ k) (hC : C < k) (hv₀ : v₀ < 1) :
    ∃ v : ℝ, (0 < v ∧ v < 1) ∧ v₀ < v ∧ ∀ Ψ : ProjectiveState → ProjectiveState,
      EntranceRadialInverseAt (referenceEntranceState k v) Ψ → ∀ δ > (0 : ℝ),
        ∃ u ∈ Ioo (0 : ℝ) δ, ∃ w ∈ Ioo (0 : ℝ) δ,
          entranceReturnValid (Ψ ![k, u, v, w]) ∧ 0 < projectiveStateDenom (Ψ ![k, u, v, w]) ∧
          entranceRadialCoordinates (Ψ ![k, u, v, w]) = ![k, u, v, w] ∧
          ContDiffAt ℝ 2 (fun z => coreRadius (entranceReturnState (Ψ z) 0)
            (entranceReturnState (Ψ z) 2)) ![k, u, v, w] ∧
          C * (u + v * (u + w) ^ 2) / k < |fderiv ℝ
            (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
            ![k, u, v, w] (Pi.single 2 1)| := by
  have hk0 : 0 < k := by linarith
  have hs0 : 0 < Real.sqrt (k ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith only [hk])
  have hlimit : C / k < k / Real.sqrt (k ^ 2 - 1) :=
    ((div_lt_one hk0).mpr hC).trans ((one_lt_div hs0).mpr ((Real.sqrt_lt' hk0).mpr (by linarith)))
  have hlarge := (tendsto_referenceEntranceHeightResponse_one (show 1 < k by linarith)).eventually
    (eventually_gt_nhds hlimit)
  have hpos : ∀ᶠ v : ℝ in 𝓝[<] 1, 0 < v :=
    (eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ v : ℝ in 𝓝[<] 1, v < 1 := self_mem_nhdsWithin
  have hnear : ∀ᶠ v : ℝ in 𝓝[<] 1, v₀ < v := (eventually_gt_nhds hv₀).filter_mono nhdsWithin_le_nhds
  obtain ⟨v, hvpos, hvlt, hvnear, Hv⟩ := (hpos.and (hlt.and (hnear.and hlarge))).exists
  have hv : 0 < v ∧ v < 1 := ⟨hvpos, hvlt⟩
  refine ⟨v, hv, hvnear, ?_⟩
  intro Ψ HΨ δ hδ
  have hk' : 7 / 4 ≤ k := by linarith
  exact HΨ.exists_referenceEntrance_positive_active_violation hk' hv Hv hδ

/-- Counterexamples occur at arbitrarily large radius, near zero waiting, inside the entrance amplitude regime. -/
theorem exists_actual_entrance_active_envelope_violation (C K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℝ, 2 ≤ k ∧ K < k ∧ ∃ v ∈ Ioo (0 : ℝ) 1, 1 - ε < v ∧
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt (referenceEntranceState k v) Ψ ∧
      ∃ u ∈ Ioo (0 : ℝ) (ε / k ^ 41), ∃ w ∈ Ioo (0 : ℝ) (ε / k ^ 41),
        entranceReturnValid (Ψ ![k, u, v, w]) ∧ 0 < projectiveStateDenom (Ψ ![k, u, v, w]) ∧
        entranceRadialCoordinates (Ψ ![k, u, v, w]) = ![k, u, v, w] ∧
        ContDiffAt ℝ 2 (fun z => coreRadius (entranceReturnState (Ψ z) 0)
          (entranceReturnState (Ψ z) 2)) ![k, u, v, w] ∧
        C * (u + v * (u + w) ^ 2) / k < |fderiv ℝ
          (fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2))
          ![k, u, v, w] (Pi.single 2 1)| := by
  let k := max 2 (max K C) + 1
  have hk : 2 ≤ k := by dsimp [k]; linarith [le_max_left (2 : ℝ) (max K C)]
  have hC : C < k := by
    dsimp [k]
    linarith [le_max_right (2 : ℝ) (max K C), le_max_right K C]
  have hK : K < k := by
    dsimp [k]
    linarith [le_max_right (2 : ℝ) (max K C), le_max_left K C]
  obtain ⟨v, hv, hvnear, HV⟩ := exists_referenceEntrance_active_envelope_violation hk hC
    (show 1 - ε < 1 by linarith)
  have hk' : 7 / 4 ≤ k := by linarith
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk' (referenceEntrance_region hk' hv) hv.1
  have hk0 : 0 < k := by linarith
  obtain ⟨u, hu, w, hw, HA⟩ := HV Ψ HΨ (ε / k ^ 41) (by positivity)
  exact ⟨k, hk, hK, v, hv, hvnear, Ψ, HΨ, u, hu, w, hw, HA⟩

end BianchiIX
