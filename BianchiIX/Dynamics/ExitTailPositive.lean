import BianchiIX.Dynamics.ExitTailArrival
import BianchiIX.Dynamics.EntranceDrift
import BianchiIX.Dynamics.CoreTailBoundary

noncomputable section

namespace BianchiIX

open Set

theorem normalized_exit_radius_antitone {x : NormalizedState} {t₀ s t h : ℝ}
    (hc : stateConstraint x = 1) (hh : 0 < h) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ r 0) :
    let β := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    (∀ r ∈ Icc s t, exitPhysicalRegion h (β r)) →
    (∀ r ∈ Icc s t, |β r 1| ≤ β r 2 / 2) → 0 ≤ β s 1 → 0 ≤ β s 3 →
    (∀ r ∈ Icc s t, 0 ≤ β r 1 ∧ 0 ≤ β r 3) ∧
      AntitoneOn (fun r => coreRadius (β r 0) (β r 2)) (Icc s t) := by
  intro β hreg hsep hu hw
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hdom (r : ℝ) (hr : r ∈ Icc s t) :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr.1)
  have hpos (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ β r 1 ∧ 0 ≤ β r 3 :=
    ⟨(normalized_projective_wall_sign (hdom s hsm) (hdom r hr) (hA s hsm) (hA r hr) 0).2.mpr hu,
      (normalized_projective_wall_sign (hdom s hsm) (hdom r hr) (hA s hsm) (hA r hr) 2).2.mpr hw⟩
  let a := fun r => 1 + normalizedMaxCurve x t₀ r 0
  let d := fun r => a r * (-coupling (β r 1) (β r 2) (β r 3) * coreRadius (β r 0) (β r 2) +
    (β r 0 - 1) / coreRadius (β r 0) (β r 2) * (β r 1 - β r 3) ^ 2)
  have hder (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun z => coreRadius (β z 0) (β z 2)) (d r) r := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hr.1)
    exact hasDerivAt_coreRadius_scaled
      (hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA r hr)) H.2.1)
      (hh.trans_le (hreg r hr).2.2.2.1.1)
  have hd (r : ℝ) (hr : r ∈ Icc s t) : d r ≤ 0 := by
    have hR : 0 ≤ coreRadius (β r 0) (β r 2) := Real.sqrt_nonneg _
    have hC : 0 ≤ coupling (β r 1) (β r 2) (β r 3) := by
      apply mul_nonneg (hpos r hr).1
      have H := (le_abs_self (β r 1)).trans (hsep r hr)
      have hv := hh.trans_le (hreg r hr).2.2.2.1.1
      linarith only [H, hv, (hpos r hr).2]
    have hM : β r 0 - 1 ≤ 0 := by linarith only [(hreg r hr).1]
    exact mul_nonpos_of_nonneg_of_nonpos (hA r hr).le
      (add_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) hR)
        (mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hM hR) (sq_nonneg _)))
  exact ⟨hpos, antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t) (HasDerivAt.continuousOn hder)
    (fun r hr => (hder r (interior_subset hr)).hasDerivWithinAt) (fun r hr => hd r (interior_subset hr))⟩

/-- D.2 holds on the whole physical tail, up to its canonical first downward arrival. -/
theorem exists_terminal_coreTail_positive_bounds {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → 0 ≤ u → 0 ≤ w → u + w ≤ b →
      let Y : CoreAngleState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let x := fromProjectiveState (coreTailEntry Y)
      let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
      coreTailValid h Y ∧ 0 < coreTailTime h Y ∧ coreTailTime h Y ≤ 16 * exitTailLength η α J ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y),
          0 ≤ β t 1 ∧ 0 ≤ β t 3 ∧
          |coreRadius (β t 0) (β t 2) - (2 + 2 * α)| + β t 1 + β t 3 ≤ C * b ∧
          2 + α < coreRadius (β t 0) (β t 2) ∧
          coreRadius (β t 0) (β t 2) ≤ 2 + 2 * α ∧ β t 1 ≤ β t 2 / 2) := by
  obtain ⟨A, hA, ε, hε, H⟩ := exists_terminal_coreTail_valid hη hJ
  refine ⟨41 * A, by linarith only [hA], ε, hε, ?_⟩
  intro α b u w hα hb hsmall hu hw hsum Y h x β
  have hwalls : |u| + |w| ≤ b := by rwa [abs_of_nonneg hu, abs_of_nonneg hw]
  obtain ⟨HV, HT, Htime, HB⟩ := H α b u w hα hb hsmall hwalls
  have h0 : (0 : ℝ) ∈ Icc 0 (coreTailTime h Y) := ⟨le_rfl, HT.le⟩
  have hAf (t : ℝ) (ht : t ∈ Icc 0 (coreTailTime h Y)) :
      0 < 1 + normalizedMaxCurve x 0 t 0 := lt_of_lt_of_le (by norm_num) (HB t ht).1
  have hD : projectiveStateDenom (coreTailEntry Y) ≠ 0 := by
    intro hz
    have H0 := hAf 0 h0
    rw [normalizedMaxCurve_initial] at H0
    change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at H0
    simp [hz] at H0
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint hD
  have hβ0 : β 0 = coreTailEntry Y := by
    dsimp only [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState hD
  have hR0 : coreRadius (β 0 0) (β 0 2) = 2 + 2 * α := by
    rw [hβ0]
    have HE := congrFun (toExitTailState_fromExitTailState
      (Y := (![2 + 2 * α, u, w] : ExitTailState))
      (by change 0 < 2 + 2 * α; linarith only [hα.1])
      (v := 1) (by change 1 ^ 2 ≤ (2 + 2 * α) ^ 2; nlinarith only [hα.1])) 0
    simpa [toExitTailState, fromExitTailState, exitTailGap, coreTailEntry, Y] using HE
  have HM := normalized_exit_radius_antitone hc (mul_pos hη.1 (pow_pos hα.1 J)) le_rfl HT.le
    hAf (fun t ht => (HB t ht).2.1) (fun t ht => (HB t ht).2.2.2.2.2)
    (by change 0 ≤ β 0 1; rw [hβ0]; exact hu) (by change 0 ≤ β 0 3; rw [hβ0]; exact hw)
  refine ⟨HV, HT, Htime, ?_⟩
  intro t ht
  have Hpos := HM.1 t ht
  have Hbound := HB t ht
  have HR := HM.2 h0 ht ht.1
  change coreRadius (β t 0) (β t 2) ≤ coreRadius (β 0 0) (β 0 2) at HR
  rw [hR0] at HR
  refine ⟨Hpos.1, Hpos.2, ?_, Hbound.2.2.2.2.1, HR,
    (le_abs_self _).trans Hbound.2.2.2.2.2⟩
  have HU := Hbound.2.2.1
  change |β t 1| + |β t 3| ≤ A * b / 2 at HU
  rw [abs_of_nonneg Hpos.1, abs_of_nonneg Hpos.2] at HU
  have HD := Hbound.2.2.2.1
  change |coreRadius (β t 0) (β t 2) - (2 + 2 * α)| ≤ 40 * A * b at HD
  nlinarith only [HD, HU, mul_nonneg (by linarith only [hA] : 0 ≤ A) hb.le]

theorem exists_terminal_coreTail_endpoint_bounds {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → 0 ≤ u → 0 ≤ w → u + w ≤ b →
      let Y : CoreAngleState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := coreTailState h Y
      coreTailValid h Y ∧ 0 < coreTailTime h Y ∧ coreTailTime h Y ≤ 16 * exitTailLength η α J ∧
        z 2 = h ∧ 0 ≤ z 1 ∧ 0 ≤ z 3 ∧
        |coreRadius (z 0) h - (2 + 2 * α)| + z 1 + z 3 ≤ C * b ∧
        2 + α < coreRadius (z 0) h ∧ coreRadius (z 0) h ≤ 2 + 2 * α := by
  obtain ⟨C, hC, ε, hε, H⟩ := exists_terminal_coreTail_positive_bounds hη hJ
  refine ⟨C, hC, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hu hw hsum Y h z
  obtain ⟨HV, HT, Htime, HB⟩ := H α b u w hα hb hsmall hu hw hsum
  have He := HB (coreTailTime h Y) ⟨HT.le, le_rfl⟩
  have Hz : z 2 = h := coreTailState_active HV
  change 0 ≤ z 1 ∧ 0 ≤ z 3 ∧
    |coreRadius (z 0) (z 2) - (2 + 2 * α)| + z 1 + z 3 ≤ C * b ∧
    2 + α < coreRadius (z 0) (z 2) ∧ coreRadius (z 0) (z 2) ≤ 2 + 2 * α ∧ _ at He
  rw [Hz] at He
  exact ⟨HV, HT, Htime, Hz, He.1, He.2.1, He.2.2.1, He.2.2.2.1, He.2.2.2.2.1⟩

end BianchiIX
