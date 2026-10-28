import BianchiIX.Dynamics.CompactReflectionEstimates
import BianchiIX.Dynamics.LongReflectionEstimates
import BianchiIX.Analysis.PositiveLogDistortion

noncomputable section

namespace BianchiIX

open Set

/-- Compact and long estimates apply to one canonical reflection map on a common amplitude domain. -/
theorem exists_reflectionReturn_phase_bounds :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      31 / 8 ≤ Y 0 → (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
      IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
        (reflectionReturnTime Y) ∧
      coreRadiusEntry (reflectionReturnState Y) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) ∧
      ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y ∧
      |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
      (∀ i : Fin 2, 0 < reflectionReturnState Y i.succ ∧ reflectionReturnState Y i.succ ≤ Y i.succ) ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ reflectionReturnState Y v
        1 / 2 ≤ d 0 ∧ |d 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (reflectionReturnState Y i.succ) * d 0 := by
  obtain ⟨εc, hεc, Cc, hCc, HC⟩ := exists_compact_reflection_estimates
  obtain ⟨εl, hεl, hεmax, HL⟩ := exists_long_reflection_estimates
  let C := max Cc 300000
  refine ⟨min εc εl, lt_min hεc hεl, (min_le_right _ _).trans hεmax,
    C, lt_of_lt_of_le hCc (le_max_left _ _), ?_⟩
  intro Y hR hu hw
  have hR0 : 0 < Y 0 := by linarith only [hR]
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1.le hw.1.le
  have hscale {K : ℝ} (hK : K ≤ C) {b : ℝ} (hb : 0 ≤ b) : K * b / Y 0 ≤ C * b / Y 0 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK hb) hR0.le
  by_cases hlong : 11 / 2 ≤ Y 0
  · have hsmall := div_le_div_of_nonneg_right (min_le_right εc εl) hR0.le
    obtain ⟨hfirst, hactual, ht, hF, hval, hwalls, hderiv⟩ := HL Y hlong
      ⟨hu.1, hu.2.trans hsmall⟩ ⟨hw.1, hw.2.trans hsmall⟩
    refine ⟨hfirst, hactual, ht, hF, hval.trans (hscale (le_max_right _ _) hb), hwalls, ?_⟩
    intro v hv0 hv1 hv2
    obtain ⟨hmargin, herr, hcone⟩ := hderiv v hv0 hv1 hv2
    exact ⟨hmargin, herr.trans (hscale (le_max_right _ _) (Real.sqrt_nonneg _)), hcone⟩
  · have hsmall : min εc εl / Y 0 ≤ εc :=
      (div_le_self (lt_min hεc hεl).le (by linarith only [hR])).trans (min_le_left _ _)
    obtain ⟨hfirst, hactual, ht, hF, hval, hwalls, hderiv⟩ := HC Y
      ⟨hR, by linarith only [lt_of_not_ge hlong]⟩ ⟨hu.1, hu.2.trans hsmall⟩ ⟨hw.1, hw.2.trans hsmall⟩
    refine ⟨hfirst, hactual, ht, hF, hval.trans (hscale (le_max_left _ _) hb), hwalls, ?_⟩
    intro v hv0 hv1 hv2
    obtain ⟨hmargin, herr, hcone⟩ := hderiv v hv0 hv1 hv2
    exact ⟨hmargin, herr.trans (hscale (le_max_left _ _) (Real.sqrt_nonneg _)), hcone⟩

/-- The canonical reflection has amplitude-dependent additive and logarithmic phase errors, with no wall gain. -/
theorem exists_reflectionReturn_estimates :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      31 / 8 ≤ Y 0 → (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
      IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
        (reflectionReturnTime Y) ∧
      coreRadiusEntry (reflectionReturnState Y) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) ∧
      ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y ∧
      |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
      (∀ i : Fin 2, 0 < reflectionReturnState Y i.succ ∧ reflectionReturnState Y i.succ ≤ Y i.succ) ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ reflectionReturnState Y v
        1 / 2 ≤ d 0 ∧ |d 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          |Real.log (d 0)| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (reflectionReturnState Y i.succ) * d 0 := by
  obtain ⟨ε, hε, hεmax, C, hC, H⟩ := exists_reflectionReturn_phase_bounds
  refine ⟨ε, hε, hεmax, 2 * C, by positivity, ?_⟩
  intro Y hR hu hw
  obtain ⟨hfirst, hactual, ht, hF, hval, hwalls, hderiv⟩ := H Y hR hu hw
  have hR0 : 0 < Y 0 := by linarith only [hR]
  have hscale {b : ℝ} (hb : 0 ≤ b) : C * b / Y 0 ≤ 2 * C * b / Y 0 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hC]) hb) hR0.le
  refine ⟨hfirst, hactual, ht, hF, hval.trans (hscale (add_nonneg hu.1.le hw.1.le)), hwalls, ?_⟩
  intro v hv0 hv1 hv2 d
  obtain ⟨hmargin, herr, hcone⟩ := hderiv v hv0 hv1 hv2
  refine ⟨hmargin, herr.trans (hscale (Real.sqrt_nonneg _)), ?_, hcone⟩
  exact ((abs_log_le_twice_sub_one_of_half_le hmargin).trans
    (mul_le_mul_of_nonneg_left herr (by norm_num))).trans_eq (by ring)

end BianchiIX
