import BianchiIX.Dynamics.ShearRestartCommonMeasurability
import BianchiIX.Dynamics.ShearRestartStatisticalPreparation

noncomputable section

namespace BianchiIX

open Set

theorem restartShearAmplitudeBudget_le_of_min {a n₂ n₃ P : ℝ}
    (ha : 0 < a ∧ a ≤ 1) (hP : 4 ≤ P) (h₂ : 0 < n₂ ∧ n₂ ≤ a)
    (h₃ : 0 < n₃ ∧ n₃ ≤ a) (hmin : min n₂ n₃ ≤ a ^ P) :
    0 < restartShearAmplitudeBudget a n₂ n₃ ∧ restartShearAmplitudeBudget a n₂ n₃ ≤ 800 * a := by
  have hp : a ^ P ≤ a ^ (4 : ℕ) := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha.2 hP
  have hprod : n₂ * n₃ ≤ a * a ^ 4 := by
    rcases min_le_iff.mp hmin with hsmall | hsmall
    · exact (mul_le_mul (hsmall.trans hp) h₃.2 h₃.1.le (by positivity)).trans_eq (mul_comm _ _)
    · exact mul_le_mul h₂.2 (hsmall.trans hp) h₃.1.le ha.1.le
  refine ⟨by dsimp [restartShearAmplitudeBudget]; positivity [ha.1, h₂.1, h₃.1], ?_⟩
  calc
    _ = 800 * (n₂ * n₃) / a ^ 4 := by unfold restartShearAmplitudeBudget; ring
    _ ≤ 800 * (a * a ^ 4) / a ^ 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by norm_num)) (by positivity)
    _ = _ := by field_simp

/-- Both small-wall orderings produce one measurable family of admissible era curves with a prescribed budget cap. -/
theorem exists_restartShear_common_statistical_preparation :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P → ∀ Bstar : ℝ, 0 < Bstar →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
          let s := q / 2 * Real.log (1 / a)
          Measurable (fun p : restartShearCommonLabelSet ε a P × Icc a (2 * a) =>
            (restartShearAmplitudeBudget a p.1.val.1 p.1.val.2,
              restartShearReturnState h s p.1.val.1 p.1.val.2 p.2)) ∧
          ∀ n₂ n₃ : ℝ, (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            min n₂ n₃ ≤ a ^ P →
            restartShearAmplitudeBudget a n₂ n₃ ∈ Ioc 0 Bstar ∧
            (restartShearEraCurve h s n₂ n₃ a).Admissible (restartShearAmplitudeBudget a n₂ n₃) ∧
            ∀ ρ ∈ Icc a (2 * a), restartShearReturnPhase h s n₂ n₃ ρ ∈ Ioo 0 1 ∧
              DifferentiableAt ℝ (restartShearReturnPhase h s n₂ n₃) ρ ∧
              1 / (4 * Real.sqrt 3) ≤ deriv (restartShearReturnPhase h s n₂ n₃) ρ ∧
              (restartShearEraCurve h s n₂ n₃ a).state (2 / restartShearReturnPhase h s n₂ n₃ ρ) =
                restartShearReturnState h s n₂ n₃ ρ := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearReturn_common_extension
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_common_bounds
  obtain ⟨hF, hhF, HF⟩ := exists_restartShearReturn_common_phase
  obtain ⟨hM, hhM, HM⟩ := exists_restartShearReturn_common_extension_measurable
  refine ⟨min hE (min hA (min hF hM)), lt_min hhE (lt_min hhA (lt_min hhF hhM)), ?_⟩
  intro h hh q D P hq hD hP Bs hBs
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  obtain ⟨aE, haE, HAE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨_, _, HFC⟩ := HF h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨aF, haF, HAF⟩ := HFC P hP
  obtain ⟨aM, haM, HAM⟩ := HM h ⟨hh.1, hh''.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aE (min aA (min aF (min aM (min (Bs / 800) (1 / 384))))),
    lt_min haE (lt_min haA (lt_min haF (lt_min haM
      (lt_min (div_pos hBs (by norm_num)) (by norm_num))))), ?_⟩
  intro a ha ε hε s
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  have ha''' := ha''.trans (min_le_right _ _)
  have harest := ha'''.trans (min_le_right _ _)
  have haB : a ≤ Bs / 800 := harest.trans (min_le_left _ _)
  have hasmall : a ≤ 1 / 384 := harest.trans (min_le_right _ _)
  have hBm : Measurable (fun p : restartShearCommonLabelSet ε a P × Icc a (2 * a) =>
      restartShearAmplitudeBudget a p.1.val.1 p.1.val.2) := by
    unfold restartShearAmplitudeBudget
    fun_prop
  refine ⟨hBm.prodMk (HAM a ⟨ha.1, ha'''.trans (min_le_left _ _)⟩ ε hε).1, ?_⟩
  intro n₂ n₃ h₂ h₃ hmin
  have hweak : 2 * ε * a ≤ a := mul_le_of_le_one_left ha.1.le (by linarith only [hε.2] : 2 * ε ≤ 1)
  have HB := restartShearAmplitudeBudget_le_of_min ⟨ha.1, hasmall.trans (by norm_num)⟩
    (by linarith only [hD, hP] : 4 ≤ P) ⟨h₂.1, h₂.2.trans hweak⟩ ⟨h₃.1, h₃.2.trans hweak⟩ hmin
  have hbudget : restartShearAmplitudeBudget a n₂ n₃ ∈ Ioc 0 Bs :=
    ⟨HB.1, HB.2.trans (by simpa only [mul_comm] using (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp haB)⟩
  obtain ⟨hu, hw, Hmatch, Hbound⟩ := HAE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin
  refine ⟨hbudget, ?_, ?_⟩
  · intro k _
    obtain ⟨hup, hwp, hsum, hdu, hdw⟩ := Hbound k
    exact ⟨hup, hwp, hsum, hu.contDiffAt, hw.contDiffAt, hdu, hdw⟩
  · intro ρ hρ
    obtain ⟨_, _, _, _, _, hklo, _⟩ := HAA a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
    obtain ⟨hdf, _, _, hdlo, _⟩ := HAF a ⟨ha.1, ha''.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ hmin ρ hρ
    have hkfour : 4 ≤ restartShearReturnState h s n₂ n₃ ρ 0 := (show 4 ≤ 1 / (96 * a) by
      apply (le_div_iff₀ (by positivity [ha.1])).mpr
      linarith only [hasmall]).trans hklo
    have hkpos : 0 < restartShearReturnState h s n₂ n₃ ρ 0 := by linarith only [hkfour]
    refine ⟨⟨div_pos (by norm_num) hkpos, (div_lt_one hkpos).mpr (by linarith only [hkfour])⟩, hdf, hdlo, ?_⟩
    have hrec : 2 / restartShearReturnPhase h s n₂ n₃ ρ = restartShearReturnState h s n₂ n₃ ρ 0 := by
      change 2 / (2 / restartShearReturnState h s n₂ n₃ ρ 0) = _
      field_simp
    rw [hrec]
    funext i
    fin_cases i
    · rfl
    · exact (Hmatch ρ hρ).1
    · exact (Hmatch ρ hρ).2.1

end BianchiIX
