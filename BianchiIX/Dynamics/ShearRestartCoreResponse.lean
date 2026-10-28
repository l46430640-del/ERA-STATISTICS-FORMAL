import BianchiIX.Dynamics.ShearRestartCoreGeometry
import BianchiIX.Dynamics.ShearRestartProjectiveResponse
import BianchiIX.Dynamics.ShearRestartFastPhaseComparison
import BianchiIX.Analysis.ReciprocalRadialBounds

noncomputable section

namespace BianchiIX

open Set

/-- A relative active-wall derivative controls the angle even when the wall is arbitrarily small. -/
theorem coreAngle_relative_radial_bound {m v : ℝ → ℝ} {a K ρ : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hm : DifferentiableAt ℝ m ρ) (hv : DifferentiableAt ℝ v ρ)
    (hvpos : 0 < v ρ) (hk : 1 / (16 * a) ≤ coreRadius (m ρ) (v ρ))
    (hmd : |deriv m ρ| ≤ K / a ^ 2) (hvd : |deriv v ρ| ≤ K * v ρ / a) :
    DifferentiableAt ℝ (fun t => coreAngle (m t) (v t)) ρ ∧
      |deriv (fun t => coreAngle (m t) (v t)) ρ| ≤ 17 * K / a := by
  let k := coreRadius (m ρ) (v ρ)
  have hkpos : 0 < k := coreRadius_pos hvpos
  have Hm : |deriv m ρ| ≤ 16 * K * k / a := hmd.trans (by
    calc
      _ = (16 * K / a) * (1 / (16 * a)) := by ring
      _ ≤ (16 * K / a) * k := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring)
  have H := hasDerivAt_coreAngle hm.hasDerivAt hv.hasDerivAt hvpos
  refine ⟨H.differentiableAt, ?_⟩
  rw [H.deriv, abs_div, abs_of_pos (mul_pos hkpos hvpos)]
  apply (div_le_iff₀ (mul_pos hkpos hvpos)).mpr
  calc
    _ ≤ |(m ρ - 1) * deriv v ρ| + |v ρ * deriv m ρ| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le ((m ρ - 1) * deriv v ρ) 0 (v ρ * deriv m ρ)
    _ = |m ρ - 1| * |deriv v ρ| + v ρ * |deriv m ρ| := by
      rw [abs_mul, abs_mul, abs_of_pos hvpos]
    _ ≤ k * (K * v ρ / a) + v ρ * (16 * K * k / a) :=
      add_le_add (mul_le_mul (coreRadius_component_bounds (m ρ) (v ρ)).1 hvd
        (abs_nonneg _) hkpos.le) (mul_le_mul_of_nonneg_left Hm hvpos.le)
    _ = (17 * K / a) * (k * v ρ) := by ring

/-- The exact shear entry has the decreasing radius scale and a relative angular derivative on one common threshold. -/
theorem exists_restartFastShearCore_response :
    ∃ hstar > (0 : ℝ), ∃ K > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 2 < q → 2 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let k := restartFastShearCoreRadius h T 1 n₂ n₃
            let z := restartFastShearCoreAngle h T 1 n₂ n₃
            T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 ∧
            DifferentiableAt ℝ k ρ ∧ 6 ≤ k ρ ∧ 1 / (16 * a) ≤ k ρ ∧ k ρ ≤ 32 / a ∧
            1 / (4096 * a ^ 2) ≤ -deriv k ρ ∧ -deriv k ρ ≤ 1536 / a ^ 2 ∧
            (0 < restartFastShearProjectiveEntry h T 1 n₂ n₃ ρ 2 →
              DifferentiableAt ℝ z ρ ∧ |deriv z ρ| ≤ K / a) := by
  obtain ⟨hG, hhG, HG⟩ := exists_restartFastShearCore_geometry
  obtain ⟨hF, hhF, HF⟩ := exists_restartFastShearProjectionPhase_approximation
  obtain ⟨hR, hhR, KR, hKR, HR⟩ := exists_restartFastShearProjectiveEntry_response
  refine ⟨min hG (min hF hR), lt_min hhG (lt_min hhF hhR), 17 * KR, by positivity, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aG, haG, HaG⟩ := HG h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  obtain ⟨KF, _, HKF⟩ := HF h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  obtain ⟨aF, haF, HaF⟩ := HKF q P hq hP
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ q hq
  refine ⟨min aG (min aF aR), lt_min haG (lt_min haF haR), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ T k z
  obtain ⟨_, _, hdom, _, _, _, hk6, hklo, hkhi, _⟩ :=
    HaG a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ ρ hρ
  obtain ⟨_, _, HFdiff, _, _, HFlo, HFhi⟩ :=
    HaF a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ h₃P ρ hρ
  obtain ⟨_, HY, HMder, Hwall, _⟩ :=
    HaR a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
      ε 1 n₂ n₃ hε (by norm_num) h₂ h₃ ρ hρ
  let f := restartFastShearProjectionPhase h T 1 n₂ n₃
  change 6 ≤ k ρ at hk6
  change 1 / (16 * a) ≤ k ρ at hklo
  change k ρ ≤ 32 / a at hkhi
  have hkpos : 0 < k ρ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk6
  have Hlo : a / 16 ≤ f ρ := by
    change a / 16 ≤ 2 / k ρ
    calc
      _ = 2 / (32 / a) := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hkpos hkhi
  have Hhi : f ρ ≤ 32 * a := by
    change 2 / k ρ ≤ 32 * a
    calc
      _ ≤ 2 / (1 / (16 * a)) := div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1]) hklo
      _ = _ := by field_simp; ring
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  have HDlo : 1 / 8 ≤ deriv f ρ := le_trans
    ((le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt2])) HFlo
  have HDhi : deriv f ρ ≤ 3 := HFhi.trans (by
    have H : (2 : ℝ) / Real.sqrt 3 ≤ 2 := div_le_self (by norm_num) hsqrt1
    linarith only [H])
  obtain ⟨HKD, _, _, HKlo, HKhi⟩ := reciprocal_radial_bounds ha.1 (by norm_num : (0 : ℝ) ≤ 3)
    HFdiff Hlo Hhi HDlo HDhi
  have heq : k = fun t => 2 / f t := by
    funext t
    change coreRadius _ _ = 2 / (2 / coreRadius _ _)
    simp
  rw [← heq] at HKD HKlo HKhi
  have HKlo' : 1 / (4096 * a ^ 2) ≤ -deriv k ρ := by norm_num at HKlo ⊢; exact HKlo
  have HKhi' : -deriv k ρ ≤ 1536 / a ^ 2 := by norm_num at HKhi ⊢; exact HKhi
  refine ⟨hdom, HKD, hk6, hklo, hkhi, HKlo', HKhi', ?_⟩
  intro hv
  exact coreAngle_relative_radial_bound ha.1 hKR.le (differentiableAt_pi.mp HY 0)
    (differentiableAt_pi.mp HY 2) hv hklo HMder (Hwall 1).2.1

end BianchiIX
