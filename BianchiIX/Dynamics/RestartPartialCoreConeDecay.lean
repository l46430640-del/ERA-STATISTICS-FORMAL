import BianchiIX.Dynamics.RestartPartialCoreCone
import BianchiIX.Analysis.RestartConeBudget

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The actual exit cone has the explicit radial rate and is uniformly as narrow as prescribed. -/
theorem exists_restartPartialCore_cone_decay :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∀ δ : ℝ, 0 < δ → ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let E := r ^ ((q - 2) / 2) + Real.sqrt (ζ / r)
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              IsLeast {t | s < t ∧ toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 t) 2 = 1} (s + T) ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                  t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
                  (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
                let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
                let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
                DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ fU ρ ∧ DifferentiableAt ℝ fP ρ ∧
                deriv f ρ < 0 ∧ 0 ≤ fU ρ ∧ 0 ≤ fP ρ ∧ C * E ≤ δ ∧
                |deriv fU ρ| ≤ C * E * Real.sqrt (fU ρ) * |deriv f ρ| ∧
                |deriv fP ρ| ≤ C * E * Real.sqrt (fP ρ) * |deriv f ρ| ∧
                |deriv fU ρ| ≤ δ * Real.sqrt (fU ρ) * |deriv f ρ| ∧
                |deriv fP ρ| ≤ δ * Real.sqrt (fP ρ) * |deriv f ρ| ∧
                (0 < fU ρ → 0 < fP ρ →
                  |deriv fU ρ| / (Real.sqrt (fU ρ) * |deriv f ρ|) +
                    |deriv fP ρ| / (Real.sqrt (fP ρ) * |deriv f ρ|) ≤ C * E) ∧
                (ζ = 0 → fP ρ = 0 ∧ deriv fP ρ = 0) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartPartialCore_radial_cone
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hC hV, lt_min hhC hhV, ?_⟩
  intro h hh L hL
  have hhC' : h ∈ Ioc (0 : ℝ) hC := ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  have hhV' : h ∈ Ioc (0 : ℝ) hV := ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
  obtain ⟨K, hK, D, hD, HK⟩ := HC h hhC' L hL
  let M := 8 * (L + 1)
  let A := (200 * coreVariationBound + 2) * K ^ 2
  let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
  let CU := 2 * D * (K + 24 * A)
  let CP := 2 * D * K * (1 + B)
  let C := 1 + CU * Real.sqrt (32 * h) + CP * Real.sqrt (2048 * M)
  have hK0 : 0 < K := by linarith only [hK]
  have hM : 0 < M := by dsimp only [M]; positivity
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have hCU : 0 ≤ CU := by dsimp only [CU]; positivity
  have hCP : 0 ≤ CP := by dsimp only [CP]; positivity
  have hCpos : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro q P hq hP δ hδ
  obtain ⟨rC, hrC, HRC⟩ := HK q P hq hP
  obtain ⟨rV, hrV, HRV⟩ := HV h hhV' L hL q (by linarith only [hq])
  obtain ⟨rB, hrB, HRB⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_core_cone_budget hCpos.le (by linarith only [hq]) (by linarith only [hP]) hδ)
  refine ⟨min rC (min rV (min rB 1)), lt_min hrC (lt_min hrV (lt_min hrB (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrV' := hr.2.trans (min_le_right _ _)
  have hrB' := hrV'.trans (min_le_right _ _)
  have hr1 : r ≤ 1 := hrB'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1
      (by linarith only [hP] : (2 : ℝ) ≤ P)
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let E := r ^ ((q - 2) / 2) + Real.sqrt (ζ / r)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hu, _, hp, _⟩ :=
    HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  change 0 < Y ρ 1 ∧ Y ρ 1 ≤ 32 * h * r ^ (q - 2) at hu
  change 0 ≤ Y ρ 2 * Y ρ 3 ∧ Y ρ 2 * Y ρ 3 ≤ 2048 * M * ζ / r ^ 3 at hp
  have HB : CU * Real.sqrt (Y ρ 1) + CP * r * Real.sqrt (Y ρ 2 * Y ρ 3) ≤ C * E :=
    restart_core_sqrt_budget hr.1 hh.1.le hM.le hζ.1 ⟨hu.1.le, hu.2⟩ hp hCU hCP
      (by dsimp only [C]; linarith)
  have Hδ : C * E ≤ δ := HRB ⟨hr.1, hrB'.trans (min_le_left _ _)⟩ ζ hζ
  have HU : CU * Real.sqrt (Y ρ 1) ≤ C * E := le_trans
    (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hCP hr.1.le) (Real.sqrt_nonneg _))) HB
  have HP : CP * r * Real.sqrt (Y ρ 2 * Y ρ 3) ≤ C * E :=
    le_trans (le_add_of_nonneg_left (by positivity)) HB
  obtain ⟨_, _, T, hT, hfirst, horig, τ, hτ, hcτ, hnear,
    hf, hfu, hfp, hslope, _, hu0, hp0, _, _, hdu, hdp, _, hzeroP⟩ :=
    HRC r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  let f := fun a => coreRadius (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 0)
    (projectiveOriginalFlow (Y a) 0 (τ (Y a)) 2)
  let fU := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 1
  let fP := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a)) 3
  have hpos : 0 < 1 / (2 * D * r ^ 2) := by positivity [hr.1]
  have hspeed := hpos.trans_le (hslope.trans (neg_le_abs _))
  have hdu' := hdu.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right HU (Real.sqrt_nonneg _)) (abs_nonneg _))
  have hdp' := hdp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right HP (Real.sqrt_nonneg _)) (abs_nonneg _))
  refine ⟨T, hT, hfirst, horig, τ, hτ, hcτ, hnear, hf, hfu, hfp,
    by linarith only [hslope, hpos], hu0, hp0, Hδ, hdu', hdp', ?_, ?_, ?_, ?_⟩
  · exact hdu'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right Hδ (Real.sqrt_nonneg _)) (abs_nonneg _))
  · exact hdp'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right Hδ (Real.sqrt_nonneg _)) (abs_nonneg _))
  · intro hfu0 hfp0
    have H₁ : |deriv fU ρ| / (Real.sqrt (fU ρ) * |deriv f ρ|) ≤ CU * Real.sqrt (Y ρ 1) :=
      (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hfu0) hspeed)).mpr (hdu.trans_eq (by ring))
    have H₂ : |deriv fP ρ| / (Real.sqrt (fP ρ) * |deriv f ρ|) ≤ CP * r * Real.sqrt (Y ρ 2 * Y ρ 3) :=
      (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hfp0) hspeed)).mpr (hdp.trans_eq (by ring))
    exact (add_le_add H₁ H₂).trans HB
  · intro hz
    have hpzero : Y ρ 2 * Y ρ 3 = 0 := by
      simp only [hz, mul_zero, zero_div] at hp
      exact le_antisymm hp.2 hp.1
    exact hzeroP hpzero

end BianchiIX
