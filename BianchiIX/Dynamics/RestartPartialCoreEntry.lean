import BianchiIX.Dynamics.RestartFastCoreRadius
import BianchiIX.Dynamics.RestartFastProjectiveEntry
import BianchiIX.Dynamics.PartialCoreEntry
import BianchiIX.Analysis.RestartCoreBudget

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The exact fast flow meets all partial-core entry conditions on one common radius scale. -/
theorem exists_restartPartialCore_entry :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∀ ε ∈ Ioc (0 : ℝ) (1 / 10000), ∃ rstar : ℝ, 0 < rstar ∧
          ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ P) →
            ∀ ρ ∈ Icc r (2 * r),
              let T := q / 2 * Real.log (1 / r)
              let y := restartFastProjectiveEntry h T θ ζ ρ
              let k := restartFastCoreRadius h T θ ζ ρ
              let z := restartFastCoreAngle h T θ ζ ρ
              let Z := Real.arsinh (4 * (8 * (L + 1)))
              0 ≤ T ∧ 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ) ∧
              T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
              0 < restartFastProjectionHeight h T θ ζ ρ ∧
              max 6 (2 * Real.cosh Z) ≤ k ∧ z ∈ Icc (-Real.arcosh k) Z ∧
              toCoreAngleState y 0 = k ∧ 0 < y 1 ∧ 0 ≤ y 2 * y 3 ∧
              y 1 + y 2 * y 3 ≤ ε / k ∧ 2 ≤ y 2 ∧
              fromCoreAngleState z (toCoreAngleState y) = y ∧ coreRegion k y := by
  obtain ⟨hK, hhK, HK⟩ := exists_restartFastCoreRadius_bounds
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hK (min hV (1 / 16)), lt_min hhK (lt_min hhV (by norm_num)), ?_⟩
  intro h hh L hL q P hq hP ε hε
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rK, hrK, HRK⟩ := HK h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q hq2
  obtain ⟨rV, hrV, HRV⟩ := HV h
    ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q hq2
  let M := 8 * (L + 1)
  let B := M + 1
  let Z := Real.arsinh (4 * M)
  have hM : 0 < M := by dsimp only [M]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hcosh : 0 < Real.cosh Z := Real.cosh_pos _
  obtain ⟨rB, hrB, HRB⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_core_budget (h := h) (M := M) hq hP hε.1)
  refine ⟨min rK (min rV (min rB (min (1 / 9)
    (min (1 / (32 * (L + 1))) (1 / (B * Real.cosh Z)))))),
    lt_min hrK (lt_min hrV (lt_min hrB (lt_min (by norm_num)
      (lt_min (by positivity) (by positivity))))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrV' := (hr.2.trans (min_le_right _ _))
  have hrB' := (hrV'.trans (min_le_right _ _))
  have hr9' := (hrB'.trans (min_le_right _ _))
  have hrL' := (hr9'.trans (min_le_right _ _))
  have hr9 : r ≤ 1 / 9 := hr9'.trans (min_le_left _ _)
  have hrL : r ≤ 1 / (32 * (L + 1)) := hrL'.trans (min_le_left _ _)
  have hrZ : r ≤ 1 / (B * Real.cosh Z) := hrL'.trans (min_le_right _ _)
  have hr1 : r ≤ 1 := hr9.trans (by norm_num)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1
      (by linarith only [hP] : (2 : ℝ) ≤ P)
  have hnorm := (restartRadialCurve_annulus hr.1 hρ hL hθ
    ⟨hζ2.1, hζ2.2.trans (by nlinarith only [hr.1, hr9])⟩).1
  have hsmall : ‖restartRadialCurve θ ζ ρ‖ ≤ 1 / 16 := by
    have H := (le_div_iff₀ (by positivity : 0 < 32 * (L + 1))).mp hrL
    linarith only [hnorm, H]
  have hhsmall : |h| ≤ 1 / 16 := by
    rw [abs_of_pos hh.1]
    exact ((hh.2.trans (min_le_right _ _)).trans (min_le_right _ _))
  have hrad := restartSectionRadicand_pos_of_small hhsmall hsmall
  let T := q / 2 * Real.log (1 / r)
  let y := restartFastProjectiveEntry h T θ ζ ρ
  let k := restartFastCoreRadius h T θ ζ ρ
  let z := restartFastCoreAngle h T θ ζ ρ
  have hT : 0 ≤ T := by
    dsimp only [T]
    apply mul_nonneg (by linarith only [hq])
    apply Real.log_nonneg
    exact (le_div_iff₀ hr.1).mpr (by simpa using hr1)
  obtain ⟨Hdom, _, hk6, hklo, hkhi, _, _⟩ :=
    HRK r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨_, _, _, _, hAlo, _, _, hv2, _, _, hu, _, hp, hz⟩ :=
    HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  change 6 ≤ k at hk6
  change 2 / (B * r) ≤ k at hklo
  change k ≤ 32 / r at hkhi
  change 2 ≤ y 2 at hv2
  change 0 < y 1 ∧ y 1 ≤ 32 * h * r ^ (q - 2) at hu
  change 0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 2048 * M * ζ / r ^ 3 at hp
  change |z| ≤ Z at hz
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk6
  have hkZ : 2 * Real.cosh Z ≤ k := by
    apply le_trans _ hklo
    apply (le_div_iff₀ (mul_pos hB hr.1)).mpr
    have H := (le_div_iff₀ (mul_pos hB hcosh)).mp hrZ
    nlinarith only [H]
  have Hbudget := HRB ⟨hr.1, hrB'.trans (min_le_left _ _)⟩
  have Hsmall : y 1 + y 2 * y 3 ≤ ε / k :=
    restart_core_amplitude_budget hr.1 hM.le hk0 hkhi ⟨hu.1.le, hu.2⟩ hp hζ.2 Hbudget
  have hv1 : 1 ≤ y 2 := le_trans (by norm_num) hv2
  have Hangle : -Real.arcosh k ≤ z :=
    (abs_le.mp (coreAngle_abs_le_arcosh hv1)).1
  have Hregion : coreRegion k y := partialCoreEntry_region hk6 hv1 hu.1.le hp.1 hε.2 Hsmall
  exact ⟨hT, hrad, Hdom, lt_of_lt_of_le (by positivity [hr.1]) hAlo,
    max_le hk6 hkZ, ⟨Hangle, (abs_le.mp hz).2⟩, rfl, hu.1, hp.1, Hsmall, hv2,
    fromCoreAngleState_toCoreAngleState (zero_lt_one.trans_le hv1), Hregion⟩

end BianchiIX
