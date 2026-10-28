import BianchiIX.Dynamics.ShearRestartReturnMeasurability
import BianchiIX.Dynamics.ShearRestartAllActivePhase
import BianchiIX.Dynamics.EraCurveStep

noncomputable section

namespace BianchiIX

open Set

def restartShearEraCurve (h s n₂ n₃ a : ℝ) : EraCurve :=
  ⟨restartShearAmplitudeExtension h s n₂ n₃ a 1, restartShearAmplitudeExtension h s n₂ n₃ a 2⟩

def restartShearAmplitudeBudget (a n₂ n₃ : ℝ) : ℝ := 800 * n₂ * n₃ / a ^ 4

/-- At a uniformly small shear scale, the exact reflected return is a measurable family of admissible era curves with any prescribed positive amplitude budget. -/
theorem exists_restartShear_statistical_preparation :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ Bstar : ℝ, 0 < Bstar →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            let s := q / 2 * Real.log (1 / a)
            Measurable (fun p : restartShearLabelSet ε a P × Icc a (2 * a) =>
              (restartShearAmplitudeBudget a p.1.val.1 p.1.val.2,
                restartShearReturnState h s p.1.val.1 p.1.val.2 p.2)) ∧
            ∀ n₂ n₃ : ℝ, (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P →
              restartShearAmplitudeBudget a n₂ n₃ ∈ Ioc 0 Bstar ∧
              (restartShearEraCurve h s n₂ n₃ a).Admissible (restartShearAmplitudeBudget a n₂ n₃) ∧
              ∀ ρ ∈ Icc a (2 * a),
                restartShearReturnPhase h s n₂ n₃ ρ ∈ Ioo 0 1 ∧
                DifferentiableAt ℝ (restartShearReturnPhase h s n₂ n₃) ρ ∧
                1 / (8 * Real.sqrt 3) ≤ deriv (restartShearReturnPhase h s n₂ n₃) ρ ∧
                (restartShearEraCurve h s n₂ n₃ a).state (2 / restartShearReturnPhase h s n₂ n₃ ρ) =
                  restartShearReturnState h s n₂ n₃ ρ := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearReturn_extension
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_output_bounds
  obtain ⟨hF, hhF, HF⟩ := exists_restartShearReturn_all_active_phase
  obtain ⟨hM, hhM, HM⟩ := exists_restartShearReturn_extension_measurable
  refine ⟨min hE (min hA (min hF hM)), lt_min hhE (lt_min hhA (lt_min hhF hhM)), ?_⟩
  intro h hh q P hq hP Bs hBs
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aA, haA, HaA⟩ := HA h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨_, _, HFC⟩ := HF h ⟨hh.1, hh''.trans (min_le_left _ _)⟩
  obtain ⟨aF, haF, HaF⟩ := HFC q P hq hP
  obtain ⟨aM, haM, HaM⟩ := HM h ⟨hh.1, hh''.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aE (min aA (min aF (min aM (min (Bs / 800) (1 / 256))))),
    lt_min haE (lt_min haA (lt_min haF (lt_min haM
      (lt_min (div_pos hBs (by norm_num)) (by norm_num))))), ?_⟩
  intro a ha ε hε s
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  have ha''' := ha''.trans (min_le_right _ _)
  have harest := ha'''.trans (min_le_right _ _)
  have haB : a ≤ Bs / 800 := harest.trans (min_le_left _ _)
  have hasmall : a ≤ 1 / 256 := harest.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := hasmall.trans (by norm_num)
  have hBm : Measurable (fun p : restartShearLabelSet ε a P × Icc a (2 * a) =>
      restartShearAmplitudeBudget a p.1.val.1 p.1.val.2) := by
    unfold restartShearAmplitudeBudget
    fun_prop
  refine ⟨hBm.prodMk (HaM a ⟨ha.1, ha'''.trans (min_le_left _ _)⟩ ε hε).1, ?_⟩
  intro n₂ n₃ h₂ h₃ h₃P
  have hn₂ : n₂ ≤ a := h₂.2.trans
    (mul_le_of_le_one_left ha.1.le (by linarith only [hε.2] : 2 * ε ≤ 1))
  have hn₃ : n₃ ≤ a ^ (4 : ℕ) := h₃P.trans (by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 hP.le)
  have hbudget : restartShearAmplitudeBudget a n₂ n₃ ∈ Ioc 0 Bs := by
    refine ⟨by dsimp [restartShearAmplitudeBudget]; positivity [ha.1, h₂.1, h₃.1], ?_⟩
    change 800 * n₂ * n₃ / a ^ 4 ≤ Bs
    calc
      _ ≤ 800 * a * a ^ 4 / a ^ 4 := div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hn₂ (by norm_num)) hn₃ h₃.1.le (by positivity [ha.1]))
        (by positivity)
      _ = 800 * a := by field_simp
      _ ≤ Bs := by simpa only [mul_comm] using (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp haB
  obtain ⟨hu, hw, Hmatch, Hbound⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P
  refine ⟨hbudget, ?_, ?_⟩
  · intro k _
    obtain ⟨hup, hwp, hsum, hdu, hdw⟩ := Hbound k
    exact ⟨hup, hwp, hsum, hu.contDiffAt, hw.contDiffAt, hdu, hdw⟩
  · intro ρ hρ
    have hklo := (HaA a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ).2.2.1
    obtain ⟨hdf, _, _, hdlo, _⟩ :=
      HaF a ⟨ha.1, ha''.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
    have hkfour : 4 ≤ restartShearReturnState h s n₂ n₃ ρ 0 := (show 4 ≤ 1 / (64 * a) by
      apply (le_div_iff₀ (by positivity [ha.1])).mpr
      linarith only [hasmall]).trans hklo
    have hkpos : 0 < restartShearReturnState h s n₂ n₃ ρ 0 := by linarith only [hkfour]
    refine ⟨⟨div_pos (by norm_num) hkpos, (div_lt_one hkpos).mpr (by linarith only [hkfour])⟩,
      hdf, hdlo, ?_⟩
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
