import BianchiIX.Dynamics.CompactPhysicalCore
import BianchiIX.Dynamics.SmallWallEntry

noncomputable section

namespace BianchiIX

open Set

/-- A fixed-height growing wall reaches a genuine core on the same Einstein orbit, with quadratic errors. -/
theorem exists_fixedWall_physical_core {c ε ν : ℝ}
    (hcpos : 0 < c) (hε : 0 < ε) (hν : 0 < ν) (hνmax : ν ≤ 1 / 4)
    (hνc : ν ^ 2 ≤ c / 4) (hνε : ν ≤ ε ^ 2 / 32) :
    ∃ Δ₀ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ Δ ∈ Icc 0 Δ₀,
      ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x → x 2 = ν →
        c ≤ rateOne (x 0) (x 1) →
        (∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i)) →
        (∀ u, 0 ≤ u → normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
        ∃ a : Fin 6, ∃ k T : ℝ, 2 ≤ k ∧ k < 8 / ε ∧ T ∈ normalizedMaxDomain x 0 ∧
          let z := (axisFrame a).map x
          let X := normalizedMaxCurve z 0 T
          let Y := toProjectiveState X
          IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain z 0 ∧ projectiveActiveWall (normalizedMaxCurve z 0 t) = 1} T ∧
            T ≤ C ∧ X = (axisFrame a).map (normalizedMaxCurve x 0 T) ∧
            Y 2 = 1 ∧ 1 < Y 0 ∧ 0 < 1 + X 0 ∧
            |coreRadius (Y 0) (Y 2) - k| ≤ C * Δ ^ 2 ∧
            referenceCoreWallFloor (8 / ε) ≤ X 3 ∧
            0 < Y 1 ∧ 0 < Y 3 ∧
            Y 1 + Y 3 ≤ Δ ^ 2 / (2 * referenceCoreWallFloor (8 / ε) ^ 2) ∧
            HasDerivAt (fun t => projectiveActiveWall (normalizedMaxCurve z 0 t))
              (normalizedEventRate projectiveActiveWall z 0 T) T ∧
            0 < normalizedEventRate projectiveActiveWall z 0 T ∧
            ContDiffAt ℝ 2 physicalEntranceData z := by
  obtain ⟨δ, hδ, C, hC, H⟩ := exists_compact_physicalEntrance_core (K := 8 / ε) (half_pos hν)
  let Δ₀ := min 1 (min (ν / 8) (min (c / 18) (min (ε * ν / 4) (δ * ν / 2))))
  have hΔ₀ : 0 < Δ₀ := by
    dsimp [Δ₀]
    positivity
  let C' := max C (2 * C / ν)
  have hCC : C ≤ C' := le_max_left _ _
  have hCnonneg : 0 ≤ C := by linarith only [hC]
  refine ⟨Δ₀, hΔ₀, C', hC.trans hCC, ?_⟩
  intro Δ hΔ x hc hp hn hr haway hprod
  have hΔ1 : Δ ≤ 1 := hΔ.2.trans (min_le_left _ _)
  have hΔν : Δ ≤ ν / 8 := hΔ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hΔc : Δ ≤ c / 18 := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hΔε : Δ ≤ ε * ν / 4 := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hΔδ : Δ ≤ δ * ν / 2 := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hsq : Δ ^ 2 ≤ Δ := by nlinarith only [hΔ.1, hΔ1]
  have hcloseε : 2 * Δ ^ 2 / ν ≤ ε / 2 := by
    apply (div_le_iff₀ hν).mpr
    nlinarith only [hsq, hΔε]
  have hcloseδ : 2 * Δ ^ 2 / ν ≤ δ := by
    apply (div_le_iff₀ hν).mpr
    nlinarith only [hsq, hΔδ]
  have hprod0 : normalizedWallProductsBound Δ x := by
    simpa only [normalizedMaxCurve_initial] using hprod 0 le_rfl
  obtain ⟨a, k, v, hk, hkε, hvlo, hvhi, _, hdist⟩ := projected_singleWall_reference hc hp
    (hn.symm ▸ hνmax) ⟨hΔ.1, hn.symm ▸ hΔν⟩ hprod0 hcpos hε hr
    (hsq.trans hΔc) (hn.symm ▸ hνc) (hn.symm ▸ hνε) (hn.symm ▸ hcloseε) haway
  rw [hn] at hvlo hdist
  let z := (axisFrame a).map x
  have hcz : stateConstraint z = 1 := ((axisFrame a).constraint x).trans hc
  have hpz : positiveWalls z := ((axisFrame a).positive x).mpr hp
  have HH := H k ⟨hk, hkε.le⟩ v ⟨hvlo, hvhi⟩ z hcz (hdist.trans hcloseδ)
  let T := (physicalEntranceData z).1
  let X := normalizedMaxCurve z 0 T
  let Y := toProjectiveState X
  obtain ⟨hfirst, htime, hV, hM, hA, hphase, hwall, hderiv, hrate, hreg⟩ := HH
  have hdom : T ∈ normalizedMaxDomain x 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 hfirst.1.1.le
  have horbit : X = (axisFrame a).map (normalizedMaxCurve x 0 T) := (axisFrame a).maxCurve hdom
  have hprodX : normalizedWallProductsBound Δ X := by
    rw [horbit]
    exact (hprod T hfirst.1.1.le).axisFrame a
  have hpX : positiveWalls X := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain z 0) (isOpen_normalizedMaxDomain z 0)
    (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain z 0)
    hfirst.1.2.1 (by simpa only [normalizedMaxCurve_initial] using hpz)
  obtain ⟨hU, hW, hweak⟩ := physical_core_weak_sum hpX hA hV hprodX
    (referenceCoreWallFloor_pos (8 / ε)) hwall
  have hphase' : |coreRadius (Y 0) (Y 2) - k| ≤ C' * Δ ^ 2 := calc
    _ ≤ C * normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) z := hphase
    _ ≤ C * (2 * Δ ^ 2 / ν) := mul_le_mul_of_nonneg_left hdist hCnonneg
    _ = (2 * C / ν) * Δ ^ 2 := by ring
    _ ≤ C' * Δ ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg Δ)
  exact ⟨a, k, T, hk, hkε, hdom, hfirst, htime.trans hCC, horbit, hV, hM, hA,
    hphase', hwall, hU, hW, hweak, hderiv, hrate, hreg⟩

end BianchiIX
