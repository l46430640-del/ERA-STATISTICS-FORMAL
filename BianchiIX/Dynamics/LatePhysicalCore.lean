import BianchiIX.Dynamics.AxisWallRates
import BianchiIX.Dynamics.LateWallEntrance
import BianchiIX.Dynamics.FixedWallPhysicalCore

noncomputable section

namespace BianchiIX

open Set

/-- Uniformly small future wall products and Taub avoidance force a core on the original orbit. -/
theorem exists_late_physical_core {ε : ℝ} (hε : 0 < ε) :
    ∃ Δ₀ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ Δ ∈ Icc 0 Δ₀,
      ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
        normalizedTaubAvoidance ε x →
        (∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
        ∃ s > (0 : ℝ), ∃ T > s, ∃ a : Fin 6, ∃ k : ℝ,
          2 ≤ k ∧ k < 8 / ε ∧ T - s ≤ C ∧ T ∈ normalizedMaxDomain x 0 ∧
          let X := (axisFrame a).map (normalizedMaxCurve x 0 T)
          let Y := toProjectiveState X
          IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧
            projectiveActiveWall ((axisFrame a).map (normalizedMaxCurve x 0 t)) = 1} T ∧
          Y 2 = 1 ∧ 1 < Y 0 ∧ 0 < 1 + X 0 ∧
          |coreRadius (Y 0) (Y 2) - k| ≤ C * Δ ^ 2 ∧
          referenceCoreWallFloor (8 / ε) ≤ X 3 ∧
          0 < Y 1 ∧ 0 < Y 3 ∧
          Y 1 + Y 3 ≤ Δ ^ 2 / (2 * referenceCoreWallFloor (8 / ε) ^ 2) ∧
          0 < fderiv ℝ projectiveActiveWall X (normalizedField X) ∧
          normalizedTaubAvoidance ε X := by
  obtain ⟨ν₀, hν₀, hν₀max, c, hcpos, _, Hentry⟩ := exists_late_fixedWall_entrance hε
  let ν := min ν₀ (min (c / 4) (ε ^ 2 / 32))
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνcap : ν ≤ ν₀ := min_le_left _ _
  have hνmax : ν ≤ 1 / 4 := hνcap.trans hν₀max
  have hνc : ν ^ 2 ≤ c / 4 := by
    have H : ν ≤ c / 4 := (min_le_right _ _).trans (min_le_left _ _)
    nlinarith only [hν, hνmax, H]
  have hνε : ν ≤ ε ^ 2 / 32 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Δ₁, hΔ₁, C, hC, Hcore⟩ := exists_fixedWall_physical_core hcpos hε hν hνmax hνc hνε
  refine ⟨min Δ₁ (ν / 8), lt_min hΔ₁ (by positivity), C, hC, ?_⟩
  intro Δ hΔ x hc hp ha hprod
  obtain ⟨r, hr, s, hrs, i, _, _, _, hhit, _, hrate, _⟩ :=
    Hentry ν hν hνcap Δ hΔ.1 (hΔ.2.trans (min_le_right _ _)) x hc hp ha hprod
  have hs : 0 < s := hr.1.trans_lt hrs
  have hdoms := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.le
  let x₀ := normalizedMaxCurve x 0 s
  have hc₀ : stateConstraint x₀ = 1 := (normalizedMaxCurve_constraint hdoms).trans hc
  have hp₀ : positiveWalls x₀ := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain x 0)
    hdoms (by simpa only [normalizedMaxCurve_initial] using hp)
  obtain ⟨j, hj⟩ := exists_axisFrame_first_wall i
  let y := (axisFrame j).map x₀
  have hcy : stateConstraint y = 1 := ((axisFrame j).constraint x₀).trans hc₀
  have hpy : positiveWalls y := ((axisFrame j).positive x₀).mpr hp₀
  have hay : normalizedTaubAvoidance ε y := (ha.forward hs.le hdoms).frame j
  have hny : y 2 = ν := by
    change wallValue 0 ((axisFrame j).map x₀) = ν
    rw [axisFrame_wallValue, hj]
    exact hhit
  have hry : c ≤ rateOne (y 0) (y 1) := by
    change c ≤ wallRate 0 ((axisFrame j).map x₀)
    rw [axisFrame_wallRate hp₀, hj]
    exact hrate
  have hprody (u : ℝ) (hu : 0 ≤ u) : normalizedWallProductsBound Δ (normalizedMaxCurve y 0 u) := by
    rw [(axisFrame j).maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc₀ 0 hu)]
    exact (normalizedWallProductsBound.forward hc hprod hs.le u hu).axisFrame j
  obtain ⟨b, k, τ, hk, hkε, _, hfirst, hτC, horbit, hV, hM, hA, hphase, hwall,
    hU, hW, hweak, _, htrans, _⟩ := Hcore Δ ⟨hΔ.1, hΔ.2.trans (min_le_left _ _)⟩
      y hcy hpy hny hry hay.initial hprody
  obtain ⟨a, hcomp⟩ := axisFrame_comp b j
  let z := (axisFrame b).map y
  have hez : z = (axisFrame a).map x₀ := hcomp x₀
  have hcz : stateConstraint z = 1 := ((axisFrame b).constraint y).trans hcy
  have hrestart (u : ℝ) (hu : s ≤ u) :
      normalizedMaxCurve z 0 (u - s) = (axisFrame a).map (normalizedMaxCurve x 0 u) := by
    rw [hez, (axisFrame a).maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc₀ 0 (sub_nonneg.mpr hu))]
    rw [(normalizedMaxCurve_restart hdoms
      (normalizedMaxDomain_contains_Ici_of_constraint hc₀ 0 (sub_nonneg.mpr hu))).2]
  have hτ : 0 < τ := hfirst.1.1
  let T := s + τ
  have hTs : s < T := by dsimp [T]; linarith only [hτ]
  have hdomT := normalizedMaxDomain_contains_Ici_of_constraint hc 0 (hs.le.trans hTs.le)
  have hend : normalizedMaxCurve z 0 τ = (axisFrame a).map (normalizedMaxCurve x 0 T) := by
    simpa only [T, add_sub_cancel_left] using hrestart T hTs.le
  let X := (axisFrame a).map (normalizedMaxCurve x 0 T)
  let Y := toProjectiveState X
  have hleast : IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧
      projectiveActiveWall ((axisFrame a).map (normalizedMaxCurve x 0 t)) = 1} T := by
    refine ⟨⟨hTs, hdomT, ?_⟩, ?_⟩
    · rw [← hend]
      exact hfirst.1.2.2
    · intro u hu
      have hh : projectiveActiveWall (normalizedMaxCurve z 0 (u - s)) = 1 := by
        rw [hrestart u hu.1.le]
        exact hu.2.2
      have H := hfirst.2 ⟨sub_pos.mpr hu.1,
        normalizedMaxDomain_contains_Ici_of_constraint hcz 0 (sub_pos.mpr hu.1).le, hh⟩
      dsimp [T]
      linarith only [H]
  have htrans' : 0 < fderiv ℝ projectiveActiveWall X (normalizedField X) := by
    change 0 < fderiv ℝ projectiveActiveWall (normalizedMaxCurve z 0 τ)
      (normalizedField (normalizedMaxCurve z 0 τ)) at htrans
    simpa only [hend] using htrans
  refine ⟨s, hs, T, hTs, a, k, hk, hkε, ?_, hdomT, hleast, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htrans',
    (ha.forward (hs.le.trans hTs.le) hdomT).frame a⟩
  · simpa only [T, add_sub_cancel_left] using hτC
  all_goals rw [← hend]; assumption

end BianchiIX
