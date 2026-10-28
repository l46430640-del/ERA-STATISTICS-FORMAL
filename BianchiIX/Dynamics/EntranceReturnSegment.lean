import BianchiIX.Dynamics.EntranceReturnDifferential
import BianchiIX.Dynamics.EntranceFlowVariation

noncomputable section

namespace BianchiIX

open Set

/-- The named first-arrival map inherits the entire entrance region from the passage construction. -/
theorem entranceReturn_region {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    ∀ t ∈ Icc 0 (entranceReturnTime y),
      entranceRegion (coreRadius (y 0) (y 2)) (projectiveOriginalFlow y 0 t) := by
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hc := fromProjectiveState_constraint hD.ne'
  have hinit : projectiveOriginalFlow y 0 0 = y := projectiveOriginalFlow_initial hD 0
  have hA : 0 < normalizedProjectiveRate (fromProjectiveState y) 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  obtain ⟨T, hT, hhit, hbefore, hreg, _⟩ := exists_normalized_entrance_first_arrival hc hk le_rfl hA
    (by change 1 ≤ projectiveOriginalFlow y 0 0 0; rwa [hinit])
    (by change coreRadius (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) = _; rw [hinit])
    (by change 0 ≤ projectiveOriginalFlow y 0 0 1 ∧ projectiveOriginalFlow y 0 0 1 ≤ _; rwa [hinit])
    (by change 0 < projectiveOriginalFlow y 0 0 2 ∧ projectiveOriginalFlow y 0 0 2 < _; rwa [hinit])
    (by change 0 ≤ projectiveOriginalFlow y 0 0 3 ∧ projectiveOriginalFlow y 0 0 3 ≤ _; rwa [hinit])
  have H := (entranceReturn_regular hk hm hu hv hw).1
  have hle : entranceReturnTime y ≤ T := H.1.2
    ⟨hT, normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le, hhit⟩
  have heq : entranceReturnTime y = T := by
    apply le_antisymm hle
    by_contra hn
    have hb := hbefore (entranceReturnTime y) ⟨H.1.1.1.le, lt_of_not_ge hn⟩
    have hh := H.1.1.2.2
    change projectiveOriginalFlow y 0 (entranceReturnTime y) 2 = 1 at hh
    change projectiveOriginalFlow y 0 (entranceReturnTime y) 2 < 1 at hb
    linarith
  rw [heq]
  exact fun t ht => (hreg t ht).2

theorem entranceReturn_walls_pos {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 < y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) :
    ∀ t ∈ Icc 0 (entranceReturnTime y),
      0 < projectiveOriginalFlow y 0 t 1 ∧ 0 < projectiveOriginalFlow y 0 t 2 ∧
      0 < projectiveOriginalFlow y 0 t 3 := by
  have H := (entranceReturn_regular hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩).1
  have hs : (0 : ℝ) ∈ Icc 0 (entranceReturnTime y) := ⟨le_rfl, H.1.1.1.le⟩
  have hD := entrance_initial_denom_pos hk hm ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩
  intro t ht
  have HP (i : Fin 3) (hi : 0 < y i.succ) : 0 < projectiveOriginalFlow y 0 t i.succ := by
    apply normalized_projective_wall_pos (H.2.1 0 hs).1 (H.2.1 t ht).1
      (H.2.1 0 hs).2 (H.2.1 t ht).2 i
    change 0 < projectiveOriginalFlow y 0 0 i.succ
    simpa only [projectiveOriginalFlow_initial hD] using hi
  exact ⟨HP 0 hu.1, HP 1 hv.1, HP 2 hw.1⟩

/-- Moving the active-wall endpoint subtracts its initial logarithmic clock variation. -/
theorem entranceReturn_clock_differential {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (w : ProjectiveState) :
    fderiv ℝ entranceReturnState y w = entranceProjectedFlowVariation y 0 (entranceReturnTime y) w -
      (w 2 / y 2) • entranceLogField (entranceReturnState y) := by
  have hhit := (entranceReturn_active_component hk hm hu hv hw).1
  have hfield : projectiveField (entranceReturnState y) 2 = entranceClockRate (entranceReturnState y) := by
    change entranceClockRate (entranceReturnState y) * entranceReturnState y 2 = _
    rw [hhit, mul_one]
  rw [(entranceReturn_differential hk hm hu hv hw w).2, hfield]
  change _ = (projectiveFlowDifferential y 0 (entranceReturnTime y) w -
    ((projectiveFlowDifferential y 0 (entranceReturnTime y) w) 2 / entranceReturnState y 2 - w 2 / y 2) •
      entranceLogField (entranceReturnState y)) - _
  rw [hhit]
  ext i
  simp only [entranceLogField, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

end BianchiIX
