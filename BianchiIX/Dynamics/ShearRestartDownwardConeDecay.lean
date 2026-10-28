import BianchiIX.Dynamics.ShearRestartDownwardCone
import BianchiIX.Analysis.RestartConeBudget

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The fixed shear return has an explicit initial-wall cone rate, uniformly as small as prescribed. -/
theorem exists_restartShearPartialCore_downward_cone_decay :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∃ C > (0 : ℝ),
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ δ > (0 : ℝ), ∃ astar > (0 : ℝ),
        ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let τ := partialCoreDownwardReturnTime
            let f := fun r => partialCoreDownwardReturnState (Y r) 0
            let fU := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 1
            let fP := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r)) 3
            let E := a ^ ((q - 2) / 2) + Real.sqrt (n₃ / a)
            1 ≤ Y ρ 2 →
            IsLeast {t | s < t ∧ toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 t) 2 = 1}
              (s + τ (Y ρ)) ∧
            DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ fU ρ ∧ DifferentiableAt ℝ fP ρ ∧
            deriv f ρ < 0 ∧ 0 ≤ fU ρ ∧ 0 ≤ fP ρ ∧ C * E ≤ δ ∧
            |deriv fU ρ| ≤ C * E * Real.sqrt (fU ρ) * |deriv f ρ| ∧
            |deriv fP ρ| ≤ C * E * Real.sqrt (fP ρ) * |deriv f ρ| ∧
            |deriv fU ρ| ≤ δ * Real.sqrt (fU ρ) * |deriv f ρ| ∧
            |deriv fP ρ| ≤ δ * Real.sqrt (fP ρ) * |deriv f ρ| ∧
            (0 < fU ρ → 0 < fP ρ →
              |deriv fU ρ| / (Real.sqrt (fU ρ) * |deriv f ρ|) +
                |deriv fP ρ| / (Real.sqrt (fP ρ) * |deriv f ρ|) ≤ C * E) ∧
            (n₃ = 0 → fP ρ = 0 ∧ deriv fP ρ = 0) := by
  obtain ⟨hC, hhC, K, hK, HC⟩ := exists_restartShearPartialCore_downward_cone
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hC hV, lt_min hhC hhV, ?_⟩
  intro h hh
  let A := (200 * coreVariationBound + 2) * K ^ 2
  let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
  let CU := 8192 * (K + 24 * A)
  let CP := 8192 * K * (1 + B)
  let C := 1 + CU * Real.sqrt (32 * h) + CP * Real.sqrt (2048 * 1)
  have hK0 : 0 < K := by linarith only [hK]
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have hCU : 0 ≤ CU := by dsimp only [CU]; positivity
  have hCP : 0 ≤ CP := by dsimp only [CP]; positivity
  have hCpos : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro q P hq hP δ hδ
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  obtain ⟨aB, haB, HaB⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_core_cone_budget hCpos.le (by linarith only [hq]) (by linarith only [hP]) hδ)
  refine ⟨min aC (min aV aB), lt_min haC (lt_min haV haB), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y τ f fU fP E hv
  have haV' := ha.2.trans (min_le_right _ _)
  obtain ⟨_, _, _, _, _, _, _, hu, _, _, _, hp⟩ :=
    HaV a ⟨ha.1, haV'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  change 0 < Y ρ 1 ∧ Y ρ 1 ≤ 8 * h * a ^ (q - 2) at hu
  change 0 ≤ Y ρ 2 * Y ρ 3 ∧ Y ρ 2 * Y ρ 3 ≤ 256 * n₂ * n₃ / a ^ 4 at hp
  have hn₂ : n₂ ≤ a := by
    have H := mul_le_mul_of_nonneg_right hε.2 ha.1.le
    nlinarith only [h₂.2, H, ha.1]
  have HUamp : 0 ≤ Y ρ 1 ∧ Y ρ 1 ≤ 32 * h * a ^ (q - 2) := ⟨hu.1.le, hu.2.trans (by
    nlinarith only [mul_nonneg hh.1.le (Real.rpow_nonneg ha.1.le (q - 2))])⟩
  have HPamp : 0 ≤ Y ρ 2 * Y ρ 3 ∧ Y ρ 2 * Y ρ 3 ≤ 2048 * 1 * n₃ / a ^ 3 := by
    refine ⟨hp.1, hp.2.trans ?_⟩
    calc
      _ ≤ 256 * a * n₃ / a ^ 4 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith only [hn₂]) h₃.1) (by positivity)
      _ = 256 * n₃ / a ^ 3 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) h₃.1) (by positivity [ha.1])
  have HB : CU * Real.sqrt (Y ρ 1) + CP * a * Real.sqrt (Y ρ 2 * Y ρ 3) ≤ C * E :=
    restart_core_sqrt_budget ha.1 hh.1.le (by norm_num : (0 : ℝ) ≤ 1) h₃.1 HUamp HPamp hCU hCP
      (by dsimp only [C]; linarith)
  have Hδ : C * E ≤ δ := HaB ⟨ha.1, haV'.trans (min_le_right _ _)⟩ n₃ ⟨h₃.1, h₃P⟩
  have HU : CU * Real.sqrt (Y ρ 1) ≤ C * E := le_trans
    (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hCP ha.1.le) (Real.sqrt_nonneg _))) HB
  have HP : CP * a * Real.sqrt (Y ρ 2 * Y ρ 3) ≤ C * E :=
    le_trans (le_add_of_nonneg_left (by positivity)) HB
  obtain ⟨_, horig, _, hf, hfu, hfp, hslope, _, hu0, hp0, _, _, hdu, hdp, _, hzeroP⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  have hpos : 0 < 1 / (8192 * a ^ 2) := by positivity [ha.1]
  have hspeed := hpos.trans_le (hslope.trans (neg_le_abs _))
  have hdu' := hdu.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right HU (Real.sqrt_nonneg _)) (abs_nonneg _))
  have hdp' := hdp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right HP (Real.sqrt_nonneg _)) (abs_nonneg _))
  refine ⟨horig, hf, hfu, hfp, by linarith only [hslope, hpos], hu0, hp0, Hδ, hdu', hdp', ?_, ?_, ?_, ?_⟩
  · exact hdu'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right Hδ (Real.sqrt_nonneg _)) (abs_nonneg _))
  · exact hdp'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right Hδ (Real.sqrt_nonneg _)) (abs_nonneg _))
  · intro hfu0 hfp0
    have H₁ : |deriv fU ρ| / (Real.sqrt (fU ρ) * |deriv f ρ|) ≤ CU * Real.sqrt (Y ρ 1) :=
      (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hfu0) hspeed)).mpr (hdu.trans_eq (by ring))
    have H₂ : |deriv fP ρ| / (Real.sqrt (fP ρ) * |deriv f ρ|) ≤ CP * a * Real.sqrt (Y ρ 2 * Y ρ 3) :=
      (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hfp0) hspeed)).mpr (hdp.trans_eq (by ring))
    exact (add_le_add H₁ H₂).trans HB
  · intro hz
    have hpzero : Y ρ 2 * Y ρ 3 = 0 := by
      simp only [hz, mul_zero, zero_div] at HPamp
      exact le_antisymm HPamp.2 HPamp.1
    exact hzeroP hpzero

end BianchiIX
