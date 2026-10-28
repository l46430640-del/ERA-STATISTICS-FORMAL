import BianchiIX.Dynamics.ShearRestartTailEntranceInputs
import BianchiIX.Dynamics.EntranceReturn

noncomputable section

namespace BianchiIX

open Set

/-- The tail's first upward arrival is the first such event after the original fast cutoff, on the original orbit. -/
theorem exists_restartShearTail_entrance_event :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 2 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let x := restartSectionChart h (restartShearCurve 1 ζ ν ρ)
          let s := q / 2 * Real.log (1 / a)
          let T := shearTailTime a D
          let y := restartShearTailProjectiveEntry h a q ζ ν T ρ
          let τ := (T + s) + entranceReturnTime y
          entranceReturnValid y ∧
          IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} τ ∧
          τ ∈ normalizedMaxDomain x 0 ∧
          entranceReturnState y = toProjectiveState (normalizedMaxCurve x 0 τ) ∧
          0 < normalizedEventRate projectiveActiveWall x 0 τ := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_entrance_inputs
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨min hI hV, lt_min hhI hhV, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨_, _, HBI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨aI, haI, HAI⟩ := HBI P hP (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq
    (by linarith only [hD]) hP
  refine ⟨min aI aV, lt_min haI haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ x s T y τ
  obtain ⟨_, hk, _, _, hm, hu, hv, hw, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, hs, hT, _, hcx, HT, _⟩ :=
    HAV a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by
    change 8 ≤ coreRadius (y 0) (y 2) at hk
    linarith only [hk]
  have Hvalid := (entranceReturn_regular hk' hm.le ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩).1
  let u := entranceReturnTime y
  have hu0 : 0 < u := Hvalid.1.1.1
  have hbaseDom : T + s ∈ normalizedMaxDomain x 0 := (HT T ⟨hT, le_rfl⟩).1
  have hbaseCon : stateConstraint (normalizedMaxCurve x 0 (T + s)) = 1 := (HT T ⟨hT, le_rfl⟩).2.2.1
  have hbaseA : 0 < 1 + normalizedMaxCurve x 0 (T + s) 0 := by
    have H := (HT T ⟨hT, le_rfl⟩).2.2.2.2.2.2.2.2.2.1
    change a ^ 2 / 10 ≤ 1 + normalizedMaxCurve x 0 (T + s) 0 at H
    exact (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le H
  have hbase : fromProjectiveState y = normalizedMaxCurve x 0 (T + s) :=
    fromProjectiveState_toProjectiveState hbaseA.ne' hbaseCon
  have Hflow (t : ℝ) (ht : 0 ≤ t) :
      normalizedMaxCurve (fromProjectiveState y) 0 t = normalizedMaxCurve x 0 ((T + s) + t) := by
    have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hbaseDom)
      (normalizedMaxDomain_contains_Ici_of_constraint hcx 0 (add_nonneg ht (add_nonneg hT hs)))
    simp only [zero_add] at H
    rw [hbase, H, add_comm t (T + s)]
  have Hrate (t : ℝ) (ht : 0 ≤ t) :
      normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t =
        normalizedEventRate projectiveActiveWall x 0 ((T + s) + t) := by
    unfold normalizedEventRate
    rw [Hflow t ht]
  have Hend : entranceReturnState y = toProjectiveState (normalizedMaxCurve x 0 τ) := by
    change toProjectiveState (normalizedMaxCurve (fromProjectiveState y) 0 u) = _
    rw [Hflow u hu0.le]
  have Hhit : toProjectiveState (normalizedMaxCurve x 0 τ) 2 = 1 := by
    have H := Hvalid.1.1.2.2
    change toProjectiveState (normalizedMaxCurve (fromProjectiveState y) 0 u) 2 = 1 at H
    rwa [Hflow u hu0.le] at H
  have Hleast : IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} τ := by
    refine ⟨⟨by dsimp only [τ]; linarith only [hu0, hT], Hhit⟩, ?_⟩
    intro t ht
    by_cases hbefore : t ≤ T + s
    · have H := HT (t - s) ⟨by linarith only [ht.1], by linarith only [hbefore]⟩
      have Hv := H.2.2.2.2.2.2.2.2.2.2.2
      change toProjectiveState (normalizedMaxCurve x 0 ((t - s) + s)) 2 < 1 at Hv
      rw [sub_add_cancel, ht.2] at Hv
      exact (lt_irrefl _ Hv).elim
    · have ht0 : 0 < t - (T + s) := sub_pos.mpr (lt_of_not_ge hbefore)
      have Hstate := Hflow (t - (T + s)) ht0.le
      rw [add_sub_cancel] at Hstate
      have Hdom := normalizedMaxDomain_contains_Ici_of_constraint
        (show stateConstraint (fromProjectiveState y) = 1 from hbase ▸ hbaseCon) 0 ht0.le
      have H := Hvalid.1.2 ⟨ht0, Hdom, ?_⟩
      · dsimp only [τ]
        linarith only [H]
      · change toProjectiveState (normalizedMaxCurve (fromProjectiveState y) 0 (t - (T + s))) 2 = 1
        rw [Hstate]
        exact ht.2
  refine ⟨Hvalid, Hleast,
    normalizedMaxDomain_contains_Ici_of_constraint hcx 0
      (show 0 ≤ (T + s) + u from add_nonneg (add_nonneg hT hs) hu0.le), Hend, ?_⟩
  rw [← Hrate u hu0.le]
  exact Hvalid.2.2.2 u ⟨hu0.le, le_rfl⟩

end BianchiIX
