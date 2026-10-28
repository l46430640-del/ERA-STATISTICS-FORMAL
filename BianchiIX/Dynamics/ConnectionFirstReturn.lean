import BianchiIX.Dynamics.ConnectionExistence
import BianchiIX.Dynamics.ConnectionMonotonicity
import BianchiIX.Analysis.MonotoneCrossing

noncomputable section

namespace BianchiIX

open Set

/-- A completed actual connection hits W = 1 for the first time and crosses V = W exactly once. -/
theorem normalized_connection_return_properties {x : NormalizedState} {t₀ μ s t : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s < t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → β s 2 = 1 →
    (0 < β s 3 ∧ β s 3 < 1) → β t 3 = 1 →
    IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain x t₀ ∧ β u 3 = 1} t ∧
      StrictAntiOn (fun u => β u 2) (Icc s t) ∧ StrictMonoOn (fun u => β u 3) (Icc s t) ∧
      (∀ u ∈ Ico s t, β u 3 < 1) ∧
      (∃! r, r ∈ Ioo s t ∧ β r 2 = β r 3) ∧
      HasDerivAt (fun u => β u 3)
        ((1 + normalizedMaxCurve x t₀ t 0) * connectionClockRate (β t)) t ∧
      0 < (1 + normalizedMaxCurve x t₀ t 0) * connectionClockRate (β t) := by
  intro β hregion hV hW hhit
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hv : 0 < β s 2 := by rw [hV]; norm_num
  obtain ⟨hVm, hWm⟩ := normalized_connection_monotonicity hc hμ hs hst.le hA hregion hv hW.1
  change StrictAntiOn (fun u => β u 2) (Icc s t) at hVm
  change StrictMonoOn (fun u => β u 3) (Icc s t) at hWm
  have hdom : t ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hst.le)
  have hfirst : IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain x t₀ ∧ β u 3 = 1} t := by
    refine ⟨⟨hst, hdom, hhit⟩, ?_⟩
    intro u hu
    by_contra hnot
    have hut : u < t := lt_of_not_ge hnot
    have H := hWm ⟨hu.1.le, hut.le⟩ htm hut
    change β u 3 < β t 3 at H
    rw [hu.2.2, hhit] at H
    exact lt_irrefl _ H
  have hsol (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt β ((1 + normalizedMaxCurve x t₀ u 0) • projectiveField (β u)) u := by
    have H := normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA u hu)) H.2.1
  have hcoord (i : Fin 4) : ContinuousOn (fun u => β u i) (Icc s t) :=
    fun u hu => (hasDerivAt_pi.mp (hsol u hu) i).continuousAt.continuousWithinAt
  have hcross := unique_crossing_of_opposite_monotonicity hst (hcoord 2) (hcoord 3) hVm hWm
    (by rw [hV]; exact hW.2) (by rw [hhit]; simpa only [hV] using hVm hsm htm hst)
  have hderiv := hasDerivAt_pi.mp (hsol t htm) 3
  change HasDerivAt (fun u => β u 3)
    ((1 + normalizedMaxCurve x t₀ t 0) * (connectionClockRate (β t) * β t 3)) t at hderiv
  rw [hhit, mul_one] at hderiv
  have hD : 0 < connectionClockRate (β t) := by
    have H := (connection_speed_bounds hμ (hregion t htm).1 (hregion t htm).2.1
      (hregion t htm).2.2.1 (hregion t htm).2.2.2).1
    change μ / 2 ≤ connectionClockRate (β t) at H
    linarith only [H, hμ]
  refine ⟨hfirst, hVm, hWm, ?_, hcross, hderiv, mul_pos (hA t htm) hD⟩
  intro u hu
  simpa only [hhit] using hWm ⟨hu.1, hu.2.le⟩ htm hu.2

/-- Full first-arrival and crossing properties in the connection entry range. -/
theorem exists_connection_first_return {μ u w : ℝ} (hμ : 4 ≤ μ)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / μ) (hw : 0 < w ∧ w ≤ 1 / 10000) :
    let x := fromProjectiveState (connectionEntry μ u w)
    let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
    ∃ T > (0 : ℝ),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ β t 3 = 1} T ∧
      (∀ t ∈ Icc 0 T, 3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x 0 t 0 ∧ connectionRegion μ (β t)) ∧
      StrictAntiOn (fun t => β t 2) (Icc 0 T) ∧ StrictMonoOn (fun t => β t 3) (Icc 0 T) ∧
      (∀ t ∈ Ico 0 T, β t 3 < 1) ∧
      (∃! r, r ∈ Ioo 0 T ∧ β r 2 = β r 3) ∧
      HasDerivAt (fun t => β t 3)
        ((1 + normalizedMaxCurve x 0 T 0) * connectionClockRate (β T)) T ∧
      0 < (1 + normalizedMaxCurve x 0 T 0) * connectionClockRate (β T) := by
  intro x β
  obtain ⟨T, hT, hhit, hprefix⟩ := exists_connection_return hμ hu hw
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμ1 : 1 ≤ μ := by linarith only [hμ]
  have hu' : 0 ≤ u ∧ u ≤ 1 / 10000 := ⟨hu.1, hu.2.trans (div_le_self (by norm_num) hμ1)⟩
  have hw' : 0 < w ∧ w < 1 := ⟨hw.1, lt_of_le_of_lt hw.2 (by norm_num)⟩
  have hD : 0 < projectiveStateDenom (connectionEntry μ u w) :=
    (connection_denom_bound (m := μ) (v := 1) hu' (by norm_num) ⟨hw.1.le, hw'.2.le⟩).2
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hβ0 : β 0 = connectionEntry μ u w := by
    dsimp [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hA (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 + normalizedMaxCurve x 0 t 0 :=
    lt_of_lt_of_le (by positivity) (hprefix t ht).1
  have H := normalized_connection_return_properties hc hμ (le_refl 0) hT hA
    (fun t ht => (hprefix t ht).2)
    (show β 0 2 = 1 by rw [hβ0]; rfl)
    (show 0 < β 0 3 ∧ β 0 3 < 1 by simpa [hβ0, connectionEntry] using hw') hhit
  exact ⟨T, hT, H.1, hprefix, H.2⟩

end BianchiIX
