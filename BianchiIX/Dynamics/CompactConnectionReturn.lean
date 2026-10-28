import BianchiIX.Dynamics.CompactTailEntrance
import BianchiIX.Dynamics.CompactEntranceDecay

noncomputable section

namespace BianchiIX

open Set

def compactConnectionEntry (η : ℝ) (Y : CoreAngleState) : ProjectiveState :=
  projectiveReflection (coreTailState η Y)

def compactConnectionTime (η : ℝ) (Y : CoreAngleState) : ℝ :=
  entranceReturnTime (compactConnectionEntry η Y) + coreTailTime η Y

def compactConnectionState (η : ℝ) (Y : CoreAngleState) : ProjectiveState :=
  entranceReturnState (compactConnectionEntry η Y)

/-- The two passages give the first new-wall arrival on one exact Einstein orbit. -/
theorem compactConnection_actual_passage {η : ℝ} {Y : CoreAngleState}
    (htail : coreTailValid η Y) (hD : 0 < projectiveStateDenom (compactConnectionEntry η Y))
    (hreturn : entranceReturnValid (compactConnectionEntry η Y)) :
    compactConnectionState η Y = projectiveReflection
      (projectiveOriginalFlow (coreTailEntry Y) 0 (compactConnectionTime η Y)) ∧
      IsLeast {t : ℝ | 0 < t ∧ projectiveReflection
        (projectiveOriginalFlow (coreTailEntry Y) 0 t) 2 = 1} (compactConnectionTime η Y) := by
  let y := compactConnectionEntry η Y
  let S := coreTailTime η Y
  let T := entranceReturnTime y
  have hS : 0 < S := htail.1.1.1
  have hT : 0 < T := hreturn.1.1.1
  have hDi := coreTailValid_denom_pos htail
  have hDs : 0 < projectiveStateDenom (coreTailState η Y) := by
    rw [← projectiveReflection_denom]
    exact hD
  have hbridge (t : ℝ) (ht : 0 ≤ t) : projectiveOriginalFlow y 0 t =
      projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (t + S)) := by
    have hdom := normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hDs.ne') 0 ht
    have href := projectiveOriginalFlow_reflection hdom
    have hre := projectiveOriginalFlow_restart hDi hS.le ht (htail.2.1 S ⟨hS.le, le_rfl⟩).2
    exact href.trans (congrArg projectiveReflection hre)
  have heq : compactConnectionState η Y = projectiveReflection
      (projectiveOriginalFlow (coreTailEntry Y) 0 (T + S)) := hbridge T hT.le
  refine ⟨heq, ⟨add_pos hT hS, ?_⟩, ?_⟩
  · change projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (T + S)) 2 = 1
    rw [← heq]
    exact hreturn.1.1.2.2
  · intro t ht
    by_cases hts : t ≤ S
    · have hsmall := htail.2.2.2.2 t ⟨ht.1.le, hts⟩
      change |projectiveOriginalFlow (coreTailEntry Y) 0 t 3| < 1 / 2 at hsmall
      have hh : projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1 := ht.2
      rw [hh, abs_one] at hsmall
      norm_num at hsmall
    · have hst : 0 < t - S := sub_pos.mpr (lt_of_not_ge hts)
      have hhit : projectiveOriginalFlow y 0 (t - S) 2 = 1 := by
        rw [hbridge (t - S) hst.le, sub_add_cancel]
        exact ht.2
      have hle := hreturn.1.2 ⟨hst,
        normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hD.ne') 0 hst.le, hhit⟩
      change T ≤ t - S at hle
      change T + S ≤ t
      linarith

/-- The finite tail can be made to satisfy any prescribed common entrance amplitude bound. -/
theorem exists_compact_connection_entrance_data {δ η : ℝ}
    (hδ : 0 < δ ∧ δ ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ δ) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (compactConnectionEntry η) Y ∧
        (7 / 4 ≤ coreRadius (compactConnectionEntry η Y 0) (compactConnectionEntry η Y 2) ∧
          coreRadius (compactConnectionEntry η Y 0) (compactConnectionEntry η Y 2) < 4) ∧
        1 ≤ compactConnectionEntry η Y 0 ∧
        (0 < compactConnectionEntry η Y 1 ∧ compactConnectionEntry η Y 1 ≤ δ) ∧
        (0 < compactConnectionEntry η Y 2 ∧ compactConnectionEntry η Y 2 ≤ 1 / 2) ∧
        compactConnectionEntry η Y 3 = η ∧
        compactConnectionEntry η Y 1 ≤ C * Y 1 ∧ compactConnectionEntry η Y 2 ≤ C * Y 2 := by
  obtain ⟨ε₀, hε₀, C, hC, HC⟩ := exists_compact_tail_entrance
    ⟨hη.1, by linarith [hη.2, hδ.2]⟩
  let ε := min ε₀ (min (δ / C) (1 / (2 * C)))
  have hε : 0 < ε := lt_min hε₀ (lt_min (div_pos hδ.1 hC) (by positivity))
  have hε₀' : ε ≤ ε₀ := min_le_left _ _
  have hεδ : ε * C ≤ δ := (le_div_iff₀ hC).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hεv : ε * C ≤ 1 / 2 := by
    have H := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (show ε ≤ 1 / (2 * C) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith only [H]
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, htime, hstate, _, hm, hrange, _, _, hform, hmult⟩ :=
    HC Y hk (by rw [abs_of_pos hu.1]; exact hu.2.trans hε₀')
      (by rw [abs_of_pos hw.1]; exact hw.2.trans hε₀')
  have hbound (i : Fin 2) : coreTailMultiplier η Y i ≤ C := by
    have H := (hmult i).2.2.2
    have hBi := (hmult i).1
    linarith only [H, inv_nonneg.mpr hBi.le,
      norm_nonneg (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y)]
  have hentry : ContDiffAt ℝ 2 (compactConnectionEntry η) Y := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (contDiffAt_pi.mp hstate 0).neg
    · exact contDiffAt_pi.mp hstate 1
    · exact contDiffAt_pi.mp hstate 3
    · exact contDiffAt_pi.mp hstate 2
  have hU : compactConnectionEntry η Y 1 = Y 1 * coreTailMultiplier η Y 0 :=
    congrFun hform 1
  have hV : compactConnectionEntry η Y 2 = Y 2 * coreTailMultiplier η Y 1 :=
    congrFun hform 2
  have hUc : compactConnectionEntry η Y 1 ≤ C * Y 1 := by
    rw [hU, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbound 0) hu.1.le
  have hVc : compactConnectionEntry η Y 2 ≤ C * Y 2 := by
    rw [hV, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbound 1) hw.1.le
  refine ⟨htail, htime, hentry, ⟨hrange.1, hrange.2.2⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    congrFun hform 3, hUc, hVc⟩
  · change 1 ≤ -coreTailState η Y 0
    linarith only [hm]
  · rw [hU]; exact mul_pos hu.1 (hmult 0).1
  · exact hUc.trans ((mul_le_mul_of_nonneg_left hu.2 hC.le).trans (by simpa only [mul_comm] using hεδ))
  · rw [hV]; exact mul_pos hw.1 (hmult 1).1
  · exact hVc.trans ((mul_le_mul_of_nonneg_left hw.2 hC.le).trans (by simpa only [mul_comm] using hεv))

end BianchiIX
