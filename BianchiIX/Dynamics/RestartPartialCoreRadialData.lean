import BianchiIX.Dynamics.RestartPartialCoreEntry
import BianchiIX.Dynamics.RestartFastEntryResponse

noncomputable section

namespace BianchiIX

open Set

/-- A common scale for the exact fast entrance and all ordinary radial data used at its return. -/
theorem exists_restartPartialCore_radial_data :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 1 ≤ K ∧ ∃ D : ℝ, 0 < D ∧
        ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let k := restartFastCoreRadius h s θ ζ
            let z := restartFastCoreAngle h s θ ζ
            let Z := Real.arsinh (4 * (8 * (L + 1)))
            r ≤ 1 ∧ 0 ≤ s ∧ 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ) ∧
            s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            0 < restartFastProjectionHeight h s θ ζ ρ ∧ DifferentiableAt ℝ Y ρ ∧
            0 ≤ Z ∧ max 6 (2 * Real.cosh Z) ≤ k ρ ∧ z ρ ≤ Z ∧
            coreRegion (k ρ) (Y ρ) ∧ 1 < Y ρ 2 ∧ Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ 1 / k ρ ∧
            2 / (K * r) ≤ k ρ ∧ k ρ ≤ K / r ∧ |deriv k ρ| ≤ K / r ^ 2 ∧
            1 / (D * r ^ 2) ≤ -deriv k ρ ∧
            |deriv (fun a => Y a 1) ρ| ≤ K * Y ρ 1 / r ∧
            |deriv (fun a => Y a 2 * Y a 3) ρ| ≤ K * (Y ρ 2 * Y ρ 3) / r ∧
            |deriv z ρ| ≤ K / r := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_entry
  obtain ⟨hR, hhR, HR⟩ := exists_restartFastCoreRadius_bounds
  obtain ⟨hD, hhD, HD⟩ := exists_restartFastEntry_radial_response
  refine ⟨min hE (min hR hD), lt_min hhE (lt_min hhR hhD), ?_⟩
  intro h hh L hL
  have hhE' : h ∈ Ioc (0 : ℝ) hE := ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  have hhR' : h ∈ Ioc (0 : ℝ) hR :=
    ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩
  have hhD' : h ∈ Ioc (0 : ℝ) hD :=
    ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩
  obtain ⟨D, hDpos, HDD⟩ := HD h hhD' L hL
  let B := 8 * (L + 1) + 1
  let J := 512 * (2 * L + 4)
  let K := 1 + B + 32 + J + D
  have hB : 0 < B := by dsimp only [B]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith only [hB, hJ, hDpos]
  have hBK : B ≤ K := by dsimp only [K]; linarith only [hJ, hDpos]
  have h32K : 32 ≤ K := by dsimp only [K]; linarith only [hB, hJ, hDpos]
  have hJK : J ≤ K := by dsimp only [K]; linarith only [hB, hDpos]
  have hDK : D ≤ K := by dsimp only [K]; linarith only [hB, hJ]
  refine ⟨K, hK, 4 * B ^ 2, by positivity, ?_⟩
  intro q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HEE⟩ := HE h hhE' L hL q P hq hP (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨rR, hrR, HRR⟩ := HR h hhR' L hL q hq2
  obtain ⟨rD, hrD, HDD'⟩ := HDD q hq2
  refine ⟨min rE (min rR (min rD 1)), lt_min hrE (lt_min hrR (lt_min hrD (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrE' : r ∈ Ioc (0 : ℝ) rE := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hrR' : r ∈ Ioc (0 : ℝ) rR :=
    ⟨hr.1, (hr.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩
  have hrD1 := ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _))
  have hrD' : r ∈ Ioc (0 : ℝ) rD := ⟨hr.1, hrD1.trans (min_le_left _ _)⟩
  have hr1 : r ≤ 1 := hrD1.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1
      (by linarith only [hP] : (2 : ℝ) ≤ P)
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let k := restartFastCoreRadius h s θ ζ
  obtain ⟨hs, hrad, hdom, hA, hk6, hangle, _, _, _, hsum, hV, _, hregion⟩ := HEE r hrE' θ ζ hθ hζ ρ hρ
  obtain ⟨_, _, _, hklo, hkhi, hdklo, hdkhi⟩ := HRR r hrR' θ ζ hθ hζ2 ρ hρ
  obtain ⟨_, hY, _, hdz, hw, _, hp, hdp, _⟩ := HDD' r hrD' θ ζ hθ hζ2 ρ hρ
  change 2 / (B * r) ≤ k ρ at hklo
  change k ρ ≤ 32 / r at hkhi
  change 1 / (4 * B ^ 2 * r ^ 2) ≤ -deriv k ρ at hdklo
  change -deriv k ρ ≤ J / r ^ 2 at hdkhi
  have hdk0 : deriv k ρ ≤ 0 := by
    have H : 0 ≤ 1 / (4 * B ^ 2 * r ^ 2) := by positivity
    linarith only [H, hdklo]
  have hdk : |deriv k ρ| ≤ K / r ^ 2 := by
    rw [abs_of_nonpos hdk0]
    exact hdkhi.trans (div_le_div_of_nonneg_right hJK (sq_nonneg r))
  have hklo' : 2 / (K * r) ≤ k ρ := le_trans
    (div_le_div_of_nonneg_left (by norm_num) (mul_pos hB hr.1)
      (mul_le_mul_of_nonneg_right hBK hr.1.le)) hklo
  have hkhi' : k ρ ≤ K / r := hkhi.trans (div_le_div_of_nonneg_right h32K hr.1.le)
  have hU := hw 0
  change 0 ≤ Y ρ 1 ∧ |deriv (fun a => Y a 1) ρ| ≤ D * Y ρ 1 / r at hU
  have hdU : |deriv (fun a => Y a 1) ρ| ≤ K * Y ρ 1 / r :=
    hU.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDK hU.1) hr.1.le)
  have hdp' : |deriv (fun a => Y a 2 * Y a 3) ρ| ≤ K * (Y ρ 2 * Y ρ 3) / r :=
    hdp.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDK hp) hr.1.le)
  have hdz' : |deriv (restartFastCoreAngle h s θ ζ) ρ| ≤ K / r :=
    hdz.trans (div_le_div_of_nonneg_right hDK hr.1.le)
  have hkpos : 0 < k ρ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) ((le_max_left _ _).trans hk6)
  have hsum' : Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ 1 / k ρ :=
    hsum.trans (div_le_div_of_nonneg_right (by norm_num) hkpos.le)
  exact ⟨hr1, hs, hrad, hdom, hA, hY, Real.arsinh_nonneg_iff.mpr (by positivity),
    hk6, hangle.2, hregion, lt_of_lt_of_le (by norm_num) hV, hsum',
    hklo', hkhi', hdk, hdklo, hdU, hdp', hdz'⟩

end BianchiIX
