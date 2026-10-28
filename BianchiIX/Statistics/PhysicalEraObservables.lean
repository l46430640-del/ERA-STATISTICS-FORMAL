import BianchiIX.Statistics.PhysicalEraSequence

noncomputable section

namespace BianchiIX.PhysicalEraSequence

open Set

variable {η : ℝ} {J : ℕ} {x : NormalizedState} {K : ℕ → ℕ+} {Y : ℕ → CoreAngleState}
variable {t : ℕ → ℝ} {a : ℕ → Fin 6} (H : PhysicalEraSequence η J x K Y t a)

include H

theorem projective_entrance (n : ℕ) :
    toProjectiveState ((axisFrame (a n)).map (normalizedMaxCurve x 0 (t n))) =
      coreRadiusEntry (Y n) := by
  have HV : coreRadiusReturnValid (Y n) := by
    simpa only [Function.iterate_zero_apply] using ((H.block n).core 0 (Nat.zero_le _)).2.2.1
  have hc : 0 < 1 + fromProjectiveState (coreRadiusEntry (Y n)) 0 := by
    simpa only [normalizedMaxCurve_initial] using (HV.2.1 0 ⟨le_rfl, HV.1.1.1.le⟩).2
  have hD : projectiveStateDenom (coreRadiusEntry (Y n)) ≠ 0 := by
    intro hz
    change 0 < 1 + (6 / projectiveStateDenom (coreRadiusEntry (Y n)) - 1) at hc
    simp only [hz, div_zero, zero_sub, add_neg_cancel, lt_self_iff_false] at hc
  rw [← H.entrance n, toProjectiveState_fromProjectiveState hD]

/-- The stored radius and phase are the geometric observables of the actual incoming section. -/
theorem entrance_observables (n : ℕ) :
    let z := toProjectiveState ((axisFrame (a n)).map (normalizedMaxCurve x 0 (t n)))
    z 2 = 1 ∧ Real.sqrt ((z 0 - 1) ^ 2 + 1) = Y n 0 ∧
      1 < Y n 0 / 2 ∧ 2 / Y n 0 ∈ Ioo (0 : ℝ) 1 ∧
      (K n : ℕ) = Nat.floor (Y n 0 / 2) := by
  have hk : 2 < Y n 0 := by
    simpa only [Function.iterate_zero_apply] using ((H.block n).core 0 (Nat.zero_le _)).1
  have hk0 : 0 < Y n 0 := lt_trans (by norm_num) hk
  rw [H.projective_entrance n]
  refine ⟨rfl, ?_, by linarith only [hk],
    ⟨div_pos (by norm_num) hk0, (div_lt_one hk0).mpr hk⟩, H.digit_eq_floor n⟩
  simpa only [coreRadius, coreEnergy, show coreRadiusEntry (Y n) 2 = 1 from rfl, one_pow] using
    coreRadius_coreRadiusEntry (Y := Y n) (lt_trans (by norm_num) hk)

/-- A global physical axis relabelling changes only the ordered frames, not the eras or their times. -/
theorem relabel (i : Fin 6) :
    ∃ b : ℕ → Fin 6, PhysicalEraSequence η J ((axisFrame i).map x) K Y t b := by
  obtain ⟨k, hk⟩ := axisFrame_inverse i
  let f := fun j : Fin 6 => (axisFrame_comp j k).choose
  have hf (j : Fin 6) (z : NormalizedState) :
      (axisFrame (f j)).map z = (axisFrame j).map ((axisFrame k).map z) :=
    ((axisFrame_comp j k).choose_spec z).symm
  have hflow (j : Fin 6) (s : ℝ) (hs : 0 ≤ s) :
      (axisFrame (f j)).map (normalizedMaxCurve ((axisFrame i).map x) 0 s) =
        (axisFrame j).map (normalizedMaxCurve x 0 s) := by
    rw [(axisFrame i).maxCurve (normalizedMaxDomain_contains_Ici_of_constraint H.constraint 0 hs), hf, hk]
  refine ⟨fun n => f (a n), ⟨((axisFrame i).constraint x).trans H.constraint, H.statistics,
    H.time_positive, H.time_strictMono, H.time_unbounded, ?_, H.block, H.next_state,
    H.next_time, ?_, ?_⟩⟩
  · intro n
    rw [hflow (a n) (t n) (H.time_positive n).le]
    exact H.entrance n
  · intro n z
    rw [hf, H.next_frame, hf]
  · obtain ⟨m, X, s, j, hblock, hs, hst, hentry, htime, hstate, hframe⟩ := H.preceding_terminal
    refine ⟨m, X, s, f j, hblock, hs, hst, ?_, htime, hstate, ?_⟩
    · rw [hflow j s hs.le]
      exact hentry
    · intro z
      rw [hf, hframe, hf]

theorem relabel_permutation (σ : Equiv.Perm (Fin 3)) :
    ∃ b : ℕ → Fin 6, PhysicalEraSequence η J ((axisPermutation σ).map x) K Y t b :=
  H.relabel (axisOrder_covers σ).choose

end BianchiIX.PhysicalEraSequence
