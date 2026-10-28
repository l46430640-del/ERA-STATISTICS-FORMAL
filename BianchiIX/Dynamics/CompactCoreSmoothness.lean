import BianchiIX.Analysis.CoordinateFactorSmoothness
import BianchiIX.Dynamics.CompactCoreFactorBounds
import BianchiIX.Dynamics.CoreReturnExitChart

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology ContDiff

/-- Smoothness belongs to the already identified first return, including zero transverse walls. -/
theorem coreRadiusReturn_contDiff_smooth {Y : CoreAngleState} (hk : 1 < Y 0)
    (hcτ : ContinuousAt coreRadiusReturnTime Y)
    (hnear : ∀ᶠ Z in 𝓝 Y, coreRadiusReturnValid Z) :
    ContDiffAt ℝ ∞ coreRadiusReturnTime Y ∧
      ContDiffAt ℝ ∞ (coreReturnState coreRadiusReturnTime) Y := by
  let T := coreRadiusReturnTime Y
  let e : CoreAngleState → NormalizedState := fun Z => fromProjectiveState (coreRadiusEntry Z)
  let F : CoreAngleState × ℝ → NormalizedState := fun z => normalizedMaxCurve (e z.1) 0 z.2
  let Q : CoreAngleState × ℝ → ℝ := fun z => projectiveActiveWall (F z)
  have H := hnear.self_of_nhds
  have ht : T ∈ normalizedMaxDomain (e Y) 0 := H.1.1.2.1
  have hA : 0 < 1 + F (Y, T) 0 := (H.2.1 T ⟨H.1.1.1.le, le_rfl⟩).2
  have hce : ContDiffAt ℝ ∞ e Y :=
    (contDiffAt_fromProjectiveState ∞ (coreRadiusReturnValid_denom_pos H).ne').comp Y
      (contDiffAt_coreRadiusEntry ∞ hk)
  have hcF : ContDiffAt ℝ ∞ F (Y, T) :=
    (contDiffAt_normalizedMaxCurve_smooth ht).comp (Y, T)
      ((hce.comp (Y, T) contDiffAt_fst).prodMk contDiffAt_snd)
  have hwall := contDiffAt_projectiveActiveWall ∞ hA.ne'
  have hcQ : ContDiffAt ℝ ∞ Q (Y, T) := hwall.comp (Y, T) hcF
  have htime : HasDerivAt (fun t => Q (Y, t))
      (normalizedEventRate projectiveActiveWall (e Y) 0 T) T := by
    convert! (hwall.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt T
      (hasDerivAt_normalizedMaxCurve ht) using 1
  have hτ : ContDiffAt ℝ ∞ coreRadiusReturnTime Y :=
    contDiffAt_scalar_event_branch (by simp) hcQ htime (ne_of_lt H.2.2.2) rfl hcτ
      (hnear.mono fun _ h => h.1.1.2.2.trans H.1.1.2.2.symm)
  have hcEnd : ContDiffAt ℝ ∞ (fun Z => F (Z, coreRadiusReturnTime Z)) Y := by
    exact hcF.comp Y (g := F) (f := fun Z => (Z, coreRadiusReturnTime Z))
      (contDiffAt_id.prodMk hτ)
  have hcProj : ContDiffAt ℝ ∞ (fun Z => toProjectiveState (F (Z, coreRadiusReturnTime Z))) Y := by
    exact (contDiffAt_toProjectiveState ∞ hA.ne').comp Y (g := toProjectiveState)
      (f := fun Z => F (Z, coreRadiusReturnTime Z)) hcEnd
  have hactive : 0 < toProjectiveState (F (Y, T)) 2 := by
    change 0 < projectiveActiveWall (F (Y, T))
    rw [H.1.1.2.2]
    norm_num
  exact ⟨hτ, (contDiffAt_toCoreAngleState ∞ hactive).comp Y hcProj⟩

theorem exists_compact_core_return_smooth :
    ∃ ε > (0 : ℝ), ∀ Y : CoreAngleState,
      (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreRadiusReturnValid Y ∧ ContDiffAt ℝ ∞ coreRadiusReturnTime Y ∧
        ContDiffAt ℝ ∞ (coreReturnState coreRadiusReturnTime) Y := by
  obtain ⟨ε, hε, _, _, hbox⟩ := exists_compact_core_return_two_germ
  refine ⟨ε, hε, ?_⟩
  intro Y hk hu hw
  have H := hbox Y hk hu hw
  exact ⟨H.1, coreRadiusReturn_contDiff_smooth (by linarith only [hk.1]) H.2.1.continuousAt
    (H.2.2.2.2.mono fun _ h => h.1)⟩

/-- Both wall multipliers and their logarithms are smooth on one signed wall neighborhood. -/
theorem exists_compact_core_smooth_factor_bounds :
    ∃ ε > (0 : ℝ), ∃ q > (0 : ℝ), q < 1 ∧ ∃ C > (0 : ℝ),
      ∀ Y : CoreAngleState, (2 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ ∞ coreRadiusReturnTime Y ∧
          ContDiffAt ℝ ∞ (coreReturnState coreRadiusReturnTime) Y ∧
          ∀ i : Fin 2,
            coreReturnState coreRadiusReturnTime Y i.succ = Y i.succ * compactCoreFactor Y i ∧
            0 < compactCoreFactor Y i ∧ compactCoreFactor Y i ≤ q ∧
            ContDiffAt ℝ ∞ (fun Z => compactCoreFactor Z i) Y ∧
            ContDiffAt ℝ ∞ (fun Z => Real.log (compactCoreFactor Z i)) Y ∧
            ‖fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y‖ ≤ C ∧
            (∀ᶠ Z in 𝓝 Y, coreReturnState coreRadiusReturnTime Z i.succ = Z i.succ * compactCoreFactor Z i) := by
  obtain ⟨ε₀, hε₀, q, hq, hq1, C, hC, hb⟩ := exists_compact_core_factor_bounds
  obtain ⟨ε₁, hε₁, hs⟩ := exists_compact_core_return_smooth
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, q, hq, hq1, C, hC, ?_⟩
  intro Y hk hu hw
  have hu₀ := hu.trans (min_le_left ε₀ ε₁)
  have hw₀ := hw.trans (min_le_left ε₀ ε₁)
  have hu₁ := hu.trans (min_le_right ε₀ ε₁)
  have hw₁ := hw.trans (min_le_right ε₀ ε₁)
  have H := hb Y hk hu₀ hw₀
  have S := hs Y hk hu₁ hw₁
  refine ⟨H.1, S.2.1, S.2.2, ?_⟩
  intro i
  have hc : ContDiffAt ℝ ∞ (fun Z => compactCoreFactor Z i) Y := by
    apply contDiffAt_coordinateFactor_smooth
    intro s hsi
    have hseg := coordinateSegment_core_box i hsi hu₁ hw₁
    have hZ := hs (coordinateSegment i.succ Y s) (by rw [hseg.1]; exact hk) hseg.2.1 hseg.2.2
    exact contDiffAt_pi.mp hZ.2.2 i.succ
  have Hi := H.2.2 i
  exact ⟨Hi.1, Hi.2.1, Hi.2.2.1, hc, hc.log Hi.2.1.ne', Hi.2.2.2.2.2⟩

end BianchiIX
