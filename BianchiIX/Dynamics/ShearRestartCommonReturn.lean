import BianchiIX.Dynamics.ShearRestartPhaseLowerBound
import BianchiIX.Dynamics.ShearRestartAllActiveOutputAmplitude
import BianchiIX.Dynamics.ShearRestartAllActiveReturn

noncomputable section

namespace BianchiIX

open Set

/-- Both small-wall orderings use one jointly C2 positive-shear return on the whole radial annulus. -/
theorem exists_restartShearReturn_common_regular :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) ∧
          ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) ((n₂, n₃), ρ) := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_joint_regular
  obtain ⟨hT, hhT, HT⟩ := exists_restartShearTail_fast_return_regular
  refine ⟨min hA hT, lt_min hhA hhT, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq (by linarith only [hD, hP])
  obtain ⟨aT, haT, HAT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aA aT, lt_min haA haT, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s
  by_cases hn₃ : n₃ ≤ a ^ P
  · exact HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃
      ⟨hε.1, hε.2.trans (by norm_num)⟩ h₂ h₃ hn₃ ρ hρ
  · exact HAT a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε
      ⟨h₂.1, (min_le_iff.mp hmin).resolve_right hn₃, h₂.2⟩ h₃ ρ hρ

/-- A single positive-shear return has the same physical endpoint and product budget in both wall orderings. -/
theorem exists_restartShearReturn_common_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
          (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
          let p := restartShearReturnParameters h s n₂ n₃ ρ
          let G := restartShearReturnState h s n₂ n₃ ρ
          let T := restartShearReturnTime h s n₂ n₃ ρ
          0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
          0 ≤ s ∧ s < T ∧ T ∈ normalizedMaxDomain x 0 ∧ connectionReturnValid p ∧
          1 / (96 * a) ≤ G 0 ∧ G 0 ≤ 128 / a ∧
          0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * n₂ * n₃ / a ^ 4 ∧
          coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve x 0 T)) := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_output_bounds
  obtain ⟨hT, hhT, HT⟩ := exists_restartShearTail_fast_output_bounds
  refine ⟨min hA (min hT (1 / 16)), lt_min hhA (lt_min hhT (by norm_num)), ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aA, haA, HAA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq (by linarith only [hD, hP])
  obtain ⟨aT, haT, HAT⟩ := HT h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ q D P hq hD hP
  refine ⟨min aA (min aT (1 / 32)), lt_min haA (lt_min haT (by norm_num)), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s x p G T
  have hasmall := (ha.2.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hε64 : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, hε.2.trans (by norm_num)⟩
  have hZ := (restartShearCurve_annulus ha.1 hρ (by norm_num : |(1 : ℝ)| = 1)
    hε64 ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩).1
  have hrad := restartSectionRadicand_pos_of_small
    (show |h| ≤ 1 / 16 by rw [abs_of_pos hh.1]; exact (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _))
    (hZ.trans (by linarith only [hasmall] : 2 * a ≤ 1 / 16))
  have hs : 0 ≤ s := mul_nonneg (by linarith only [hq])
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa only [one_mul] using hasmall.trans (by norm_num : (1 : ℝ) / 32 ≤ 1))))
  have H : connectionReturnValid p ∧ s < T ∧ 1 / (96 * a) ≤ G 0 ∧ G 0 ≤ 128 / a ∧
      0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * n₂ * n₃ / a ^ 4 ∧
      coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve x 0 T)) := by
    by_cases hn₃ : n₃ ≤ a ^ P
    · obtain ⟨hp, ht, hlo, hhi, hu, hw, hsum, horbit⟩ := HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
        ε n₂ n₃ hε64 h₂ h₃ hn₃ ρ hρ
      refine ⟨hp, ht, ?_, hhi.trans ?_, hu, hw, hsum, horbit⟩
      · exact (one_div_le_one_div_of_le (by positivity [ha.1] : 0 < 64 * a)
          (by nlinarith only [ha.1] : 64 * a ≤ 96 * a)).trans hlo
      · exact div_le_div_of_nonneg_right (by norm_num : (64 : ℝ) ≤ 128) ha.1.le
    · exact HAT a ⟨ha.1, (ha.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ ε n₂ n₃ hε
        ⟨h₂.1, (min_le_iff.mp hmin).resolve_right hn₃, h₂.2⟩ h₃ ρ hρ
  exact ⟨hrad, hs, H.2.1,
    normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 (hs.trans H.2.1.le),
    H.1, H.2.2⟩

/-- The complete phase estimate uses one reference function across the two wall orderings. -/
theorem exists_restartShearReturn_common_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 3 < q → 4 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 < n₂ ∧ n₂ ≤ 2 * ε * a) →
            (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → min n₂ n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let X := restartShearReturnPhase h s n₂ n₃
            let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 n₂ n₃ r)
            DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
            |deriv X ρ - deriv F ρ| ≤ C * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨hA, hhA, HA⟩ := exists_restartShearReturn_all_active_phase_quarter
  obtain ⟨hT, hhT, HT⟩ := exists_restartShearTail_fast_output_phase_quarter
  refine ⟨min hA hT, lt_min hhA hhT, ?_⟩
  intro h hh q D hq hD
  obtain ⟨CA, hCA, HCA⟩ := HA h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  obtain ⟨CT, hCT, HCT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D hq hD
  refine ⟨max CA CT, hCA.trans_le (le_max_left _ _), ?_⟩
  intro P hP
  obtain ⟨aA, haA, HAA⟩ := HCA q P hq (by linarith only [hD, hP])
  obtain ⟨aT, haT, HAT⟩ := HCT P hP
  refine ⟨min aA aT, lt_min haA haT, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ hmin ρ hρ s X F
  by_cases hn₃ : n₃ ≤ a ^ P
  · obtain ⟨hd, hv, he, hlo, hhi⟩ := HAA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃
      ⟨hε.1, hε.2.trans (by norm_num)⟩ h₂ h₃ hn₃ ρ hρ
    exact ⟨hd, hv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg a)),
      he.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ha.1.le), hlo, hhi.trans (le_max_left _ _)⟩
  · obtain ⟨hd, hv, he, hlo, hhi⟩ := HAT a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε
      ⟨h₂.1, (min_le_iff.mp hmin).resolve_right hn₃, h₂.2⟩ h₃ ρ hρ
    exact ⟨hd, hv.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg a)),
      he.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) ha.1.le), hlo, hhi.trans (le_max_right _ _)⟩

end BianchiIX
