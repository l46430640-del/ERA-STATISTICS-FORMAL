import BianchiIX.Dynamics.ShearRestartPartialCoreEntry
import BianchiIX.Dynamics.ShearRestartCoreResponse

noncomputable section

namespace BianchiIX

open Set

/-- One scale supplies all radial data for actual shear entrances, including their incoming boundary. -/
theorem exists_restartShearPartialCore_radial_data :
    ∃ hstar > (0 : ℝ), ∃ K ≥ (1 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let z := restartFastShearCoreAngle h s 1 n₂ n₃
            1 ≤ Y ρ 2 →
            a ≤ 1 ∧ 0 ≤ s ∧ 0 < restartSectionRadicand h (restartShearCurve 1 n₂ n₃ ρ) ∧
            s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            0 < restartFastShearHeight h s 1 n₂ n₃ ρ ∧ DifferentiableAt ℝ Y ρ ∧
            6 ≤ k ρ ∧ coreRegion (k ρ) (Y ρ) ∧
            (1 < Y ρ 2 ∨ (Y ρ 2 = 1 ∧ 1 ≤ Y ρ 0)) ∧ z ρ ≤ 0 ∧
            Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ 1 / k ρ ∧
            2 / (K * a) ≤ k ρ ∧ k ρ ≤ K / a ∧ |deriv k ρ| ≤ K / a ^ 2 ∧
            1 / (4096 * a ^ 2) ≤ -deriv k ρ ∧
            |deriv (fun r => Y r 1) ρ| ≤ K * Y ρ 1 / a ∧
            |deriv (fun r => Y r 2 * Y r 3) ρ| ≤ K * (Y ρ 2 * Y ρ 3) / a ∧
            |deriv z ρ| ≤ K / a := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hC, hhC, KC, hKC, HC⟩ := exists_restartFastShearCore_response
  obtain ⟨hR, hhR, KR, hKR, HR⟩ := exists_restartFastShearProjectiveEntry_response
  let K := 2000 + KC + KR
  have hK : 1 ≤ K := by dsimp only [K]; linarith only [hKC, hKR]
  have h32K : 32 ≤ K := by dsimp only [K]; linarith only [hKC, hKR]
  have h1536K : 1536 ≤ K := by dsimp only [K]; linarith only [hKC, hKR]
  have hCK : KC ≤ K := by dsimp only [K]; linarith only [hKR]
  have hRK : KR ≤ K := by dsimp only [K]; linarith only [hKC]
  refine ⟨min hE (min hC hR), lt_min hhE (lt_min hhC hhR), K, hK, ?_⟩
  intro h hh q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  have hP2 : 2 < P := by linarith only [hP]
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aC, haC, HaC⟩ := HC h
    ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q P hq2 hP2
  obtain ⟨aR, haR, HaR⟩ := HR h
    ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ q hq2
  refine ⟨min aE (min aC (min aR 1)), lt_min haE (lt_min haC (lt_min haR (by norm_num))), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k z hv
  have haC' := ha.2.trans (min_le_right _ _)
  have haR' := haC'.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := haR'.trans (min_le_right _ _)
  obtain ⟨hs, hrad, hdom, hA, _, hk, _, _, _, _, _, hsum, Hentry⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  obtain ⟨hz, _, hregion, hvcase⟩ := Hentry hv
  obtain ⟨_, _, _, hklo, hkhi, hdklo, hdkhi, Hangle⟩ :=
    HaC a ⟨ha.1, haC'.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  obtain ⟨_, HY, _, Hwall, _, hp, hdp, _⟩ :=
    HaR a ⟨ha.1, haR'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  change 1 / (16 * a) ≤ k ρ at hklo
  change k ρ ≤ 32 / a at hkhi
  change 1 / (4096 * a ^ 2) ≤ -deriv k ρ at hdklo
  change -deriv k ρ ≤ 1536 / a ^ 2 at hdkhi
  have hdk0 : deriv k ρ ≤ 0 := by
    have H : 0 ≤ 1 / (4096 * a ^ 2) := by positivity
    linarith only [H, hdklo]
  have hdk : |deriv k ρ| ≤ K / a ^ 2 := by
    rw [abs_of_nonpos hdk0]
    exact hdkhi.trans (div_le_div_of_nonneg_right h1536K (sq_nonneg a))
  have hklo' : 2 / (K * a) ≤ k ρ := by
    calc
      _ ≤ 2 / (32 * a) := div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1])
        (mul_le_mul_of_nonneg_right h32K ha.1.le)
      _ = 1 / (16 * a) := by ring
      _ ≤ _ := hklo
  have hkhi' : k ρ ≤ K / a := hkhi.trans (div_le_div_of_nonneg_right h32K ha.1.le)
  have hdU : |deriv (fun r => Y r 1) ρ| ≤ K * Y ρ 1 / a := (Hwall 0).2.1.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRK (Hwall 0).1) ha.1.le)
  have hdp' : |deriv (fun r => Y r 2 * Y r 3) ρ| ≤ K * (Y ρ 2 * Y ρ 3) / a := hdp.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRK hp) ha.1.le)
  have hdz : |deriv z ρ| ≤ K / a :=
    (Hangle (zero_lt_one.trans_le hv)).2.trans (div_le_div_of_nonneg_right hCK ha.1.le)
  have hkpos : 0 < k ρ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have hsum' : Y ρ 1 + Y ρ 2 * Y ρ 3 ≤ 1 / k ρ :=
    hsum.trans (div_le_div_of_nonneg_right (by norm_num) hkpos.le)
  exact ⟨ha1, hs, hrad, hdom, hA, HY, hk, hregion, hvcase, hz.2, hsum',
    hklo', hkhi', hdk, hdklo, hdU, hdp', hdz⟩

end BianchiIX
