import BianchiIX.Dynamics.LatePhysicalCore
import BianchiIX.Dynamics.AwayCorePhase
import BianchiIX.Dynamics.CoreSectionPhysical

noncomputable section

namespace BianchiIX

open Set

/-- A common late product threshold produces an arbitrarily small core in a compact phase range. -/
theorem exists_late_compact_core {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ γ > (0 : ℝ), γ < 1 / 4 ∧ ∀ B : ℝ, 0 < B →
      ∃ Δ₀ > (0 : ℝ), ∀ Δ ∈ Icc 0 Δ₀,
        ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
          normalizedTaubAvoidance ε x →
          (∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
          ∃ T > (0 : ℝ), ∃ a : Fin 6, ∃ Y : CoreAngleState,
            T ∈ normalizedMaxDomain x 0 ∧
            fromProjectiveState (coreRadiusEntry Y) = (axisFrame a).map (normalizedMaxCurve x 0 T) ∧
            Y ∈ compactEraPhase N γ ∧ 0 < Y 1 ∧ 0 < Y 2 ∧ Y 1 + Y 2 ≤ B ∧
            normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) ∧
            0 < fderiv ℝ projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y))
              (normalizedField (fromProjectiveState (coreRadiusEntry Y))) := by
  obtain ⟨N, γ, hγ, hγmax, B₀, hB₀, Hphase⟩ := exists_compactEraPhase_of_taub_avoidance hε
  obtain ⟨Δ₁, hΔ₁, C, hC, Hcore⟩ := exists_late_physical_core hε
  have hCpos : 0 < C := by linarith only [hC]
  let n := referenceCoreWallFloor (8 / ε)
  have hn : 0 < n := referenceCoreWallFloor_pos _
  refine ⟨N, γ, hγ, hγmax, ?_⟩
  intro B hB
  let b := min B B₀
  have hb : 0 < b := lt_min hB hB₀
  let Δ₀ := min Δ₁ (min 1 (min (γ / (2 * C)) (2 * b * n ^ 2)))
  have hΔ₀ : 0 < Δ₀ := by dsimp [Δ₀]; positivity
  refine ⟨Δ₀, hΔ₀, ?_⟩
  intro Δ hΔ x hc hp ha hprod
  have hΔC : Δ ≤ Δ₁ := hΔ.2.trans (min_le_left _ _)
  have hΔ1 : Δ ≤ 1 := hΔ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hΔγ : Δ ≤ γ / (2 * C) := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hΔb : Δ ≤ 2 * b * n ^ 2 := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsq : Δ ^ 2 ≤ Δ := by nlinarith only [hΔ.1, hΔ1]
  have herror : C * Δ ^ 2 ≤ γ / 2 := by
    have H := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hΔγ
    have Hsq := mul_le_mul_of_nonneg_left hsq hCpos.le
    nlinarith only [H, Hsq]
  have hamp : Δ ^ 2 / (2 * n ^ 2) ≤ b := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * n ^ 2)).mpr
    nlinarith only [hsq, hΔb]
  obtain ⟨s, hs, T, hTs, a, k, hk, _, _, hdom, _, hV, hM, hA, hphase,
    _, hU, hW, hweak, htrans, havoid⟩ := Hcore Δ ⟨hΔ.1, hΔC⟩ x hc hp ha hprod
  let X := (axisFrame a).map (normalizedMaxCurve x 0 T)
  let y := toProjectiveState X
  let Y : CoreAngleState := ![coreRadius (y 0) (y 2), y 1, y 3]
  have hlow : 2 - γ / 2 ≤ Y 0 := by
    have Hlo := (abs_le.mp hphase).1
    change 2 - γ / 2 ≤ coreRadius (y 0) (y 2)
    change -(C * Δ ^ 2) ≤ coreRadius (y 0) (y 2) - k at Hlo
    linarith only [Hlo, hk, herror]
  have hsum : Y 1 + Y 2 ≤ b := hweak.trans hamp
  have hcX : stateConstraint X = 1 := ((axisFrame a).constraint _).trans
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have hcoords : toCoreAngleState y = Y := by
    change y 2 = 1 at hV
    simp only [toCoreAngleState, hV, one_mul, Y]
  have hentry : coreRadiusEntry Y = y := by
    rw [← hcoords]
    exact coreRadiusEntry_of_upward_section hM.le hV
  have hphysical : fromProjectiveState (coreRadiusEntry Y) = X := by
    rw [hentry]
    exact fromProjectiveState_toProjectiveState hA.ne' hcX
  have havoidY : normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) := by
    rw [hphysical]
    exact havoid
  refine ⟨T, hs.trans hTs, a, Y, hdom, hphysical,
    Hphase Y hlow hU hW (hsum.trans (min_le_right _ _)) havoidY,
    hU, hW, hsum.trans (min_le_left _ _), havoidY, ?_⟩
  rwa [hphysical]

end BianchiIX
