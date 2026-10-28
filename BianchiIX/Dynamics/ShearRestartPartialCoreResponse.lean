import BianchiIX.Dynamics.ShearRestartPartialCoreEntry
import BianchiIX.Dynamics.ShearRestartCoreResponse
import BianchiIX.Dynamics.PartialCoreRadialCurve

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem restartFastShearProjectiveEntry_flow {h s σ n₂ n₃ ρ t : ℝ}
    (hrad : 0 ≤ restartSectionRadicand h (restartShearCurve σ n₂ n₃ ρ))
    (hs : 0 ≤ s) (hA : 0 < restartFastShearHeight h s σ n₂ n₃ ρ) (ht : 0 ≤ t) :
    projectiveOriginalFlow (restartFastShearProjectiveEntry h s σ n₂ n₃ ρ) 0 t =
      toProjectiveState (normalizedMaxCurve (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 (s + t)) := by
  have hc := restartSectionChart_constraint hrad
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hbase := fromProjectiveState_toProjectiveState hA.ne'
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hdom)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))
  simp only [zero_add] at H
  change toProjectiveState (normalizedMaxCurve
    (fromProjectiveState (toProjectiveState (normalizedMaxCurve _ 0 s))) 0 t) = _
  rw [hbase, H, add_comm t s]

/-- The ordinary first-return radius and reciprocal phase estimates apply to the exact shear family. -/
theorem exists_restartShearPartialCore_radial_response :
    ∃ hstar > (0 : ℝ), ∃ K ≥ (1 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let U := fun r => Y r 1
            let p := fun r => Y r 2 * Y r 3
            let C := 4096 * coreVariationBound
            1 < Y ρ 2 →
            s ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            (∀ t : ℝ, 0 ≤ t → projectiveOriginalFlow (Y ρ) 0 t = toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 (s + t))) ∧
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              IsLeast {t | s < t ∧ toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 t) 2 = 1} (s + T) ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ),
                  IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
                    projectiveOriginalFlow y 0 t 2 = 1} (τ y) ∧
                  ∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
                    0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0) ∧
                let f := fun r => coreRadius (projectiveOriginalFlow (Y r) 0 (τ (Y r)) 0)
                  (projectiveOriginalFlow (Y r) 0 (τ (Y r)) 2)
                DifferentiableAt ℝ f ρ ∧ k ρ / 2 ≤ f ρ ∧ f ρ ≤ 2 * k ρ ∧
                DifferentiableAt ℝ (fun r => f r - k r) ρ ∧
                |f ρ - k ρ| ≤ 16 * K * (U ρ + a * (p ρ) ^ 2) ∧
                |deriv (fun r => f r - k r) ρ| ≤ 4 * C * K ^ 2 * (U ρ + a * p ρ) / a ^ 2 ∧
                DifferentiableAt ℝ (fun r => 2 / f r - 2 / k r) ρ ∧
                |2 / f ρ - 2 / k ρ| ≤ 32 * K ^ 3 * a ^ 2 * (U ρ + a * (p ρ) ^ 2) ∧
                |deriv (fun r => 2 / f r - 2 / k r) ρ| ≤
                  (8 * C * K ^ 4 + 64 * K ^ 5) * (U ρ + a * p ρ) := by
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
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k U p C hv
  have haC' := ha.2.trans (min_le_right _ _)
  have haR' := haC'.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := haR'.trans (min_le_right _ _)
  obtain ⟨hs, hrad, hdom, hA, _, hk, _, _, _, _, _, _, Hentry⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  obtain ⟨_, _, hregion, _⟩ := Hentry hv.le
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
  have hdU : |deriv U ρ| ≤ K * U ρ / a := (Hwall 0).2.1.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRK (Hwall 0).1) ha.1.le)
  have hdp' : |deriv p ρ| ≤ K * p ρ / a := hdp.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hRK hp) ha.1.le)
  have hdz : |deriv (restartFastShearCoreAngle h s 1 n₂ n₃) ρ| ≤ K / a :=
    (Hangle (zero_lt_one.trans hv)).2.trans (div_le_div_of_nonneg_right hCK ha.1.le)
  obtain ⟨T, hT, hfirst, Hreturn⟩ := exists_partialCore_radial_curve_response ⟨ha.1, ha1⟩ hK HY
    hk hregion hv hklo' hkhi' hdk hdU hdp' hdz
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  refine ⟨hdom, Hflow, T, hT, hfirst, ?_, Hreturn⟩
  refine ⟨⟨by linarith only [hT], ?_⟩, ?_⟩
  · rw [← Hflow T hT.le]
    exact hfirst.1.2
  · intro t ht
    have hsub : 0 < t - s := sub_pos.mpr ht.1
    have HF := Hflow (t - s) hsub.le
    rw [add_sub_cancel] at HF
    have Hleast := hfirst.2 ⟨hsub, by rw [HF]; exact ht.2⟩
    linarith only [Hleast]

end BianchiIX
