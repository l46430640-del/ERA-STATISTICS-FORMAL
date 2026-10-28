import BianchiIX.Dynamics.RestartReturnMeasurability
import BianchiIX.Dynamics.RestartReturnControl
import BianchiIX.Dynamics.EraCurveStep

noncomputable section

namespace BianchiIX

open Set

def restartEraCurve (h s θ ζ r : ℝ) : EraCurve :=
  ⟨restartAmplitudeExtension h s θ ζ r 1, restartAmplitudeExtension h s θ ζ r 2⟩

def restartAmplitudeBudget (L r ζ : ℝ) : ℝ := 6400 * (8 * (L + 1)) * ζ / r ^ 3

/-- The same actual restart, extended curve, and radial phase obey a prescribed era budget. -/
theorem exists_restart_statistical_preparation :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ Bstar : ℝ, 0 < Bstar →
        ∃ rstar > (0 : ℝ), ∀ r ∈ Ioc (0 : ℝ) rstar,
          let s := q / 2 * Real.log (1 / r)
          Measurable (fun p : restartLabelSet L r P × Icc r (2 * r) =>
            (restartAmplitudeBudget L r p.1.val.2, restartReturnState h s p.1.val.1 p.1.val.2 p.2)) ∧
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            restartAmplitudeBudget L r ζ ∈ Ioc 0 Bstar ∧
            (restartEraCurve h s θ ζ r).Admissible (restartAmplitudeBudget L r ζ) ∧
            ∀ ρ ∈ Icc r (2 * r),
              restartReturnPhase h s θ ζ ρ ∈ Ioo 0 1 ∧
              DifferentiableAt ℝ (restartReturnPhase h s θ ζ) ρ ∧
              1 / (8 * Real.sqrt 3) ≤ deriv (restartReturnPhase h s θ ζ) ρ ∧
              (restartEraCurve h s θ ζ r).state (2 / restartReturnPhase h s θ ζ ρ) =
                restartReturnState h s θ ζ ρ := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartReturn_extension
  obtain ⟨hC, hhC, HC⟩ := exists_restartReturn_control
  obtain ⟨hM, hhM, HM⟩ := exists_restartReturn_extension_measurable
  refine ⟨min hE (min hC hM), lt_min hhE (lt_min hhC hhM), ?_⟩
  intro h hh L hL q P hq hP Bs hBs
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨C, _, HCL⟩ := HC h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ L hL
  obtain ⟨rC, hrC, HRC⟩ := HCL q P hq hP
  obtain ⟨rM, hrM, HRM⟩ := HM h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ L hL q P hq hP
  let K : ℝ := 6400 * (8 * (L + 1))
  let A : ℝ := 8 * (L + 1) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hAp : 0 < A := by dsimp [A]; positivity
  let rstar := min rE (min rC (min rM (min 1 (min (Bs / K) (1 / (8 * A))))))
  have hrs : 0 < rstar := lt_min hrE (lt_min hrC (lt_min hrM (lt_min (by norm_num)
    (lt_min (div_pos hBs hK) (by positivity)))))
  refine ⟨rstar, hrs, ?_⟩
  intro r hr s
  have hrpos := hr.1
  have hre : r ≤ rE := hr.2.trans (min_le_left _ _)
  have hrc : r ≤ rC := hr.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrm : r ≤ rM := hr.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrrest : r ≤ min 1 (min (Bs / K) (1 / (8 * A))) :=
    hr.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hr1 : r ≤ 1 := hrrest.trans (min_le_left _ _)
  have hrB : r ≤ Bs / K := hrrest.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrsmall : r ≤ 1 / (8 * A) := hrrest.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hBm : Measurable (fun p : restartLabelSet L r P × Icc r (2 * r) => restartAmplitudeBudget L r p.1.val.2) := by
    unfold restartAmplitudeBudget
    fun_prop
  refine ⟨hBm.prodMk (HRM r ⟨hr.1, hrm⟩).1, ?_⟩
  intro θ ζ hθ hζ
  have hζpos := hζ.1
  have hζ4 : ζ ≤ r ^ 4 := hζ.2.trans (by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith : (4 : ℝ) ≤ P))
  have hbudget : restartAmplitudeBudget L r ζ ∈ Ioc 0 Bs := by
    refine ⟨by dsimp [restartAmplitudeBudget]; positivity, ?_⟩
    change K * ζ / r ^ 3 ≤ Bs
    calc
      _ ≤ K * r ^ 4 / r ^ 3 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hζ4 hK.le) (by positivity)
      _ = K * r := by field_simp
      _ ≤ Bs := by simpa only [mul_comm] using (le_div_iff₀ hK).mp hrB
  obtain ⟨hu, hw, Hmatch, Hbound⟩ := HRE r ⟨hr.1, hre⟩ θ ζ hθ hζ
  refine ⟨hbudget, ?_, ?_⟩
  · intro k _
    obtain ⟨hup, hwp, hsum, hdu, hdw⟩ := Hbound k
    exact ⟨hup, hwp, hsum, hu.contDiffAt, hw.contDiffAt, hdu, hdw⟩
  · intro ρ hρ
    obtain ⟨_, _, _, hklo, _, _, _, _, _, hdf, _, _, hdlo, _⟩ :=
      HRC r ⟨hr.1, hrc⟩ θ ζ hθ hζ ρ hρ
    have hmul : r * (8 * A) ≤ 1 := (le_div_iff₀ (by positivity : 0 < 8 * A)).mp hrsmall
    have hkfour : 4 ≤ restartReturnState h s θ ζ ρ 0 := (show 4 ≤ 1 / (2 * A * r) by
      apply (le_div_iff₀ (by positivity : 0 < 2 * A * r)).mpr
      nlinarith).trans hklo
    have hkpos : 0 < restartReturnState h s θ ζ ρ 0 := by linarith
    have hfunit : restartReturnPhase h s θ ζ ρ ∈ Ioo 0 1 :=
      ⟨div_pos (by norm_num) hkpos, (div_lt_one hkpos).mpr (by linarith)⟩
    refine ⟨hfunit, hdf, hdlo, ?_⟩
    have hrec : 2 / restartReturnPhase h s θ ζ ρ = restartReturnState h s θ ζ ρ 0 := by
      change 2 / (2 / restartReturnState h s θ ζ ρ 0) = _
      field_simp
    rw [hrec]
    funext i
    fin_cases i
    · rfl
    · exact (Hmatch ρ hρ).1
    · exact (Hmatch ρ hρ).2.1

end BianchiIX
