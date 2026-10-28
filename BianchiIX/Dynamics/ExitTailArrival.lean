import BianchiIX.Dynamics.ExitFirstHit

noncomputable section

namespace BianchiIX

open Set

theorem coreTailEntry_terminal_region {α u w h : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hu : |u| ≤ 1 / 100) (hw : |w| ≤ 1 / 100) (hh : h ≤ 1) :
    exitPhysicalRegion h (coreTailEntry ![2 + 2 * α, u, w]) ∧
      coreRadius (coreTailEntry ![2 + 2 * α, u, w] 0) 1 = 2 + 2 * α := by
  let Y : ExitTailState := ![2 + 2 * α, u, w]
  have hR : 0 < Y 0 := by change 0 < 2 + 2 * α; linarith only [hα.1]
  have hv : (1 : ℝ) ^ 2 ≤ (Y 0) ^ 2 := by change 1 ^ 2 ≤ (2 + 2 * α) ^ 2; nlinarith only [hα.1]
  have heq : coreTailEntry Y = fromExitTailState 1 Y := by
    ext i
    fin_cases i <;> simp [coreTailEntry, fromExitTailState, exitTailGap]
  have hr := congrFun (toExitTailState_fromExitTailState hR hv) 0
  change coreRadius (fromExitTailState 1 Y 0) 1 = Y 0 at hr
  rw [← heq] at hr
  change coreRadius (coreTailEntry ![2 + 2 * α, u, w] 0) 1 = 2 + 2 * α at hr
  refine ⟨⟨?_, ?_, hu, ⟨hh, le_rfl⟩, hw⟩, hr⟩
  · have H := (exitTailGap_compact (R := 2 + 2 * α) (by linarith only [hα.1]) (v := 1) (by norm_num)).1
    change 1 - Real.sqrt ((2 + 2 * α) ^ 2 - 1) ≤ 0
    simpa only [exitTailGap, one_pow, sub_nonpos] using H
  · change 7 / 4 ≤ coreRadius (coreTailEntry ![2 + 2 * α, u, w] 0) 1 ∧
      coreRadius (coreTailEntry ![2 + 2 * α, u, w] 0) 1 ≤ 17 / 4
    rw [hr]
    constructor <;> linarith only [hα.1, hα.2]

/-- The canonical tail map exists at the D.1 height, uniformly in alpha and in signed wall ratios. -/
theorem exists_terminal_coreTail_valid {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : CoreAngleState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let x := fromProjectiveState (coreTailEntry Y)
      let β := fun t => toProjectiveState (normalizedMaxCurve x 0 t)
      coreTailValid h Y ∧ 0 < coreTailTime h Y ∧ coreTailTime h Y ≤ 16 * exitTailLength η α J ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y),
          1 / 8 ≤ 1 + normalizedMaxCurve x 0 t 0 ∧
          exitPhysicalRegion h (β t) ∧
          |β t 1| + |β t 3| ≤ A * b / 2 ∧
          |coreRadius (β t 0) (β t 2) - (2 + 2 * α)| ≤ 40 * A * b ∧
          2 + α < coreRadius (β t 0) (β t 2) ∧ |β t 1| ≤ β t 2 / 2) := by
  obtain ⟨A, hA, ε₀, hε₀, HE⟩ := exists_normalized_exit_arrival hη hJ
  let ε := min ε₀ (1 / 1000)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  refine ⟨A, hA, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hwalls Y h x β
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have hh1 : h ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.1.le
    dsimp only [h]
    nlinarith only [H, hη.2]
  have hbε : b ≤ ε := hsmall.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hε.le)
  have hbs : b ≤ 1 / 1000 := hbε.trans (min_le_right _ _)
  have hu : |u| ≤ 1 / 100 := by linarith only [hwalls, hbs, abs_nonneg w]
  have hw : |w| ≤ 1 / 100 := by linarith only [hwalls, hbs, abs_nonneg u]
  obtain ⟨hentry, hRentry⟩ := coreTailEntry_terminal_region hα hu hw hh1
  change exitPhysicalRegion h (coreTailEntry Y) at hentry
  have hD := (exitPhysicalRegion_denom hh hentry).1
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hβ0 : β 0 = coreTailEntry Y := by
    dsimp only [β]
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  have hA0 : 0 < 1 + normalizedMaxCurve x 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hV0 : β 0 2 = 1 := by rw [hβ0]; rfl
  have hM0 : β 0 0 < 0 := by rw [hβ0]; exact (exitPhysicalRegion_phase_bounds hh hentry).2
  have hR0 : coreRadius (β 0 0) (β 0 2) = 2 + 2 * α := by rw [hβ0]; exact hRentry
  have hw0 : |β 0 1| + |β 0 3| ≤ b := by rw [hβ0]; exact hwalls
  obtain ⟨T, hT, hhit, hreg, htime, H⟩ := HE x 0 0 α b hc le_rfl hα hb
    (hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le J))) hA0 hM0 hV0 hR0 hw0
  have hAf (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 + normalizedMaxCurve x 0 t 0 :=
    lt_of_lt_of_le (by norm_num) (hreg t ht).1
  have HF := normalized_exit_first_hit hc hh le_rfl hT hAf (fun t ht => (hreg t ht).2) hhit
  have hcanonical : coreTailTime h Y = T := HF.1.csInf_eq
  have hvalid : coreTailValid h Y := by
    dsimp only [coreTailValid]
    rw [hcanonical]
    refine ⟨HF.1, ?_, HF.2.2.1, HF.2.2.2, ?_⟩
    · intro t ht
      exact ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1, hAf t ht⟩
    · intro t ht
      exact lt_of_le_of_lt (hreg t ht).2.2.2.2.2 (by norm_num)
  refine ⟨hvalid, by rwa [hcanonical], ?_, ?_⟩
  · rw [hcanonical]
    simpa only [sub_zero] using htime
  · intro t ht
    rw [hcanonical] at ht
    have HB := H t ht
    have HA := normalized_exit_chart_lower hh (ne_of_gt (hAf t ht))
      (normalizedMaxCurve_forward_of_constraint hc ht.1).2.1 (hreg t ht).2
    refine ⟨HA, (hreg t ht).2, HB.1, ?_, HB.2.2⟩
    have HR := HB.2.1
    change |coreRadius (β t 0) (β t 2) - coreRadius (β 0 0) (β 0 2)| ≤ 40 * A * b at HR
    rwa [hR0] at HR

end BianchiIX
