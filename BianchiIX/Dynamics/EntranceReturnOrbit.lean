import BianchiIX.Dynamics.EntranceReturn
import BianchiIX.Dynamics.FlowComposition

noncomputable section

namespace BianchiIX

open Set

/-- Attach the canonical entrance return to an existing orbit without losing its first-arrival property. -/
theorem entranceReturn_existing_orbit {x : NormalizedState} {s : ℝ} {y : ProjectiveState}
    (hc : stateConstraint x = 1) (hs : 0 ≤ s)
    (hy : toProjectiveState (normalizedMaxCurve x 0 s) = y)
    (hprefix : ∀ r ∈ Icc 0 s, 0 < 1 + normalizedMaxCurve x 0 r 0 ∧
      projectiveActiveWall (normalizedMaxCurve x 0 r) < 1)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    let T := s + entranceReturnTime y
    entranceReturnValid y ∧ ContDiffAt ℝ 2 entranceReturnTime y ∧ ContDiffAt ℝ 2 entranceReturnState y ∧
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
        projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
      (∀ r ∈ Icc 0 T, 0 < 1 + normalizedMaxCurve x 0 r 0) ∧
      (∀ r ∈ Ico 0 T, projectiveActiveWall (normalizedMaxCurve x 0 r) < 1) ∧
      toProjectiveState (normalizedMaxCurve x 0 T) = entranceReturnState y ∧
      0 < normalizedEventRate projectiveActiveWall x 0 T := by
  intro T
  have HR := entranceReturn_regular hk hm hu hv hw
  have HV := HR.1
  have ht : 0 < entranceReturnTime y := HV.1.1.1
  have hT : 0 < T := add_pos_of_nonneg_of_pos hs ht
  have hdom : s ∈ normalizedMaxDomain x 0 := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hbase : fromProjectiveState y = normalizedMaxCurve x 0 s := by
    rw [← hy]
    exact fromProjectiveState_toProjectiveState (hprefix s ⟨hs, le_rfl⟩).1.ne'
      (normalizedMaxCurve_forward_of_constraint hc hs).2.1
  have hflow (r : ℝ) (hr : r ∈ Icc 0 (entranceReturnTime y)) :
      normalizedMaxCurve x 0 (s + r) = normalizedMaxCurve (fromProjectiveState y) 0 r := by
    have hdr : s + r - s ∈ normalizedMaxDomain (normalizedMaxCurve x 0 s) 0 := by
      rw [← hbase, add_sub_cancel_left]
      exact (HV.2.1 r hr).1
    simpa only [← hbase, add_sub_cancel_left] using (normalizedMaxCurve_restart hdom hdr).2
  have hbefore (r : ℝ) (hr : r ∈ Ico 0 T) : projectiveActiveWall (normalizedMaxCurve x 0 r) < 1 := by
    by_cases hrs : r ≤ s
    · exact (hprefix r ⟨hr.1, hrs⟩).2
    · have hsr : s < r := lt_of_not_ge hrs
      have hsub : r - s ∈ Ico 0 (entranceReturnTime y) := ⟨by linarith only [hsr], by dsimp only [T] at hr; linarith only [hr.2]⟩
      have HF := hflow (r - s) ⟨hsub.1, hsub.2.le⟩
      have HE := HV.2.2.1 (r - s) hsub
      rw [← HF] at HE
      simpa only [add_sub_cancel] using HE
  have hlast : normalizedMaxCurve x 0 T = normalizedMaxCurve (fromProjectiveState y) 0 (entranceReturnTime y) :=
    hflow _ ⟨ht.le, le_rfl⟩
  refine ⟨HV, HR.2.1, HR.2.2.1, ?_, ?_, hbefore, ?_, ?_⟩
  · refine ⟨⟨hT, normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le, ?_⟩, ?_⟩
    · rw [hlast]
      exact HV.1.1.2.2
    · intro r hr
      by_contra hn
      have H := hbefore r ⟨hr.1.le, lt_of_not_ge hn⟩
      linarith only [H, hr.2.2]
  · intro r hr
    by_cases hrs : r ≤ s
    · exact (hprefix r ⟨hr.1, hrs⟩).1
    · have hsub : r - s ∈ Icc 0 (entranceReturnTime y) := ⟨by linarith only [lt_of_not_ge hrs], by dsimp only [T] at hr; linarith only [hr.2]⟩
      have HF := hflow (r - s) hsub
      have HE := (HV.2.1 (r - s) hsub).2
      rw [← HF] at HE
      simpa only [add_sub_cancel] using HE
  · rw [hlast]
    rfl
  · change 0 < fderiv ℝ projectiveActiveWall (normalizedMaxCurve x 0 T) (normalizedField (normalizedMaxCurve x 0 T))
    rw [hlast]
    exact HV.2.2.2 _ ⟨ht.le, le_rfl⟩

end BianchiIX
