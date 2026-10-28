import BianchiIX.Algebra.TwoStageRadiusResponse
import BianchiIX.Dynamics.EntranceReflectionValues
import BianchiIX.Dynamics.ShearRestartEntranceConnectionCurve

noncomputable section

namespace BianchiIX

open Set

/-- A bounded total radius displacement and an inverse-scale derivative error hold
uniformly through the preceding entrance, core, and long connection. -/
theorem exists_restartShearEntrance_radius_comparison :
    ∃ hstar > (0 : ℝ), ∃ C > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let g := fun r => restartShearReturnState h s n₂ n₃ r 0
            Y ρ 2 < 1 → DifferentiableAt ℝ k ρ ∧ DifferentiableAt ℝ g ρ ∧
              1 / (64 * a) ≤ k ρ ∧ 1 / (64 * a) ≤ g ρ ∧
              |g ρ - k ρ| ≤ C ∧ |deriv k ρ| ≤ C / a ^ 2 ∧
              |deriv g ρ - deriv k ρ| ≤ C / a := by
  obtain ⟨hI, hhI, _, _, HI⟩ := exists_restartShearEntrance_differential_inputs
  obtain ⟨hR, hhR, B, hB, HR⟩ := exists_restartShearEntrance_radial_response
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearEntrance_core_cone
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearEntrance_connection_curve
  let C := B + 50000
  have hCpos : 0 < C := by dsimp only [C]; linarith only [hB]
  refine ⟨min hI (min hR (min hC hG)), lt_min hhI (lt_min hhR (lt_min hhC hhG)), C, hCpos, ?_⟩
  intro h hh q P hq hP
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  obtain ⟨aI, haI, HaI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aG, haG, HaG⟩ := HG h ⟨hh.1, hh''.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aI (min aR (min aC (min aG 1))),
    lt_min haI (lt_min haR (lt_min haC (lt_min haG zero_lt_one))), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k g hv
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  have ha''' := ha''.trans (min_le_right _ _)
  have ha1 : a ≤ 1 := ha'''.trans (min_le_right _ _)
  obtain ⟨HY, hk8, hklo, _, hm, hu, hv', hw, hsmall, _⟩ :=
    HaI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, hκ6, hκlo, _, Hval, Hder, _, Hκder⟩ :=
    HaR a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, hκneg, hfneg, Hcore, Hbounds, _⟩ :=
    HaC a ⟨ha.1, ha''.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨HGdiff, _, _, _, _, _, Hconn, _⟩ :=
    HaG a ⟨ha.1, ha'''.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let κ := fun r => coreRadius (entranceReturnState (Y r) 0) (entranceReturnState (Y r) 2)
  let f := fun r => partialCoreDownwardReturnState (Y r) 0
  have HV := entrancePartialCore_reflection_values hk8 hm.le hu hv' hw
    ⟨by norm_num, le_rfl⟩ hsmall
  change κ ρ / 2 ≤ restartShearReturnParameters h s n₂ n₃ ρ 0 ∧
    (1 ≤ κ ρ - g ρ ∧ κ ρ - g ρ ≤ 3) ∧ κ ρ / 2 ≤ g ρ ∧ g ρ ≤ κ ρ ∧ _ at HV
  change 6 ≤ κ ρ at hκ6
  change 1 / (32 * a) ≤ κ ρ at hκlo
  change |κ ρ - k ρ| ≤ B * a at Hval
  change |deriv κ ρ - deriv k ρ| ≤ B / a at Hder
  change -deriv κ ρ ≤ 1537 / a ^ 2 at Hκder
  change deriv κ ρ < 0 at hκneg
  change deriv f ρ < 0 at hfneg
  have hκpos : 0 < κ ρ := by linarith only [hκ6]
  have hratio : |deriv f ρ / deriv κ ρ| ≤ 5 / 4 := by
    rw [abs_of_nonneg (div_pos_of_neg_of_neg hfneg hκneg).le]
    exact Hbounds.2
  have Hd := two_stage_radius_response hκpos HV.1 hκneg.ne hfneg.ne hratio Hcore Hconn
  have hκabs : |deriv κ ρ| ≤ 1537 / a ^ 2 := by rwa [abs_of_neg hκneg]
  have Hgκ : |deriv g ρ - deriv κ ρ| ≤ 49184 / a := Hd.trans (by
    calc
      _ ≤ (1537 / a ^ 2) / (1 / (32 * a)) :=
        div_le_div₀ (by positivity) hκabs (by positivity [ha.1]) hκlo
      _ = _ := by field_simp; ring)
  have Hk : DifferentiableAt ℝ k ρ := differentiableAt_pi.mp
    (((contDiffAt_toCoreAngleState 1 hv'.1).differentiableAt (by norm_num)).comp ρ HY) 0
  have Hg : DifferentiableAt ℝ g ρ := differentiableAt_pi.mp (HGdiff.differentiableAt (by norm_num)) 0
  refine ⟨Hk, Hg, ?_, ?_, ?_, ?_, ?_⟩
  · change 1 / (16 * a) ≤ k ρ at hklo
    exact (div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1]) (by linarith only [ha.1])).trans hklo
  · calc
      _ = (1 / (32 * a)) / 2 := by ring
      _ ≤ κ ρ / 2 := div_le_div_of_nonneg_right hκlo (by norm_num)
      _ ≤ _ := HV.2.2.1
  · have Hdiff : |g ρ - κ ρ| ≤ 3 := by
      rw [abs_of_nonpos (sub_nonpos.mpr HV.2.2.2.1)]
      linarith only [HV.2.1.2]
    have Hsum := (abs_sub_le (g ρ) (κ ρ) (k ρ)).trans (add_le_add Hdiff Hval)
    have HB := mul_le_of_le_one_right hB.le ha1
    dsimp only [C]
    linarith only [Hsum, HB]
  · have hBa : B / a ≤ B / a ^ 2 := div_le_div_of_nonneg_left hB.le (by positivity [ha.1])
      (by nlinarith only [mul_le_mul_of_nonneg_left ha1 ha.1.le])
    calc
      _ = |deriv κ ρ - (deriv κ ρ - deriv k ρ)| := by congr 1; ring
      _ ≤ |deriv κ ρ| + |deriv κ ρ - deriv k ρ| := abs_sub _ _
      _ ≤ 1537 / a ^ 2 + B / a ^ 2 := add_le_add hκabs (Hder.trans hBa)
      _ = (1537 + B) / a ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by dsimp only [C]; linarith) (sq_nonneg a)
  · calc
      _ ≤ |deriv g ρ - deriv κ ρ| + |deriv κ ρ - deriv k ρ| := abs_sub_le _ _ _
      _ ≤ 49184 / a + B / a := add_le_add Hgκ Hder
      _ = (49184 + B) / a := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by dsimp only [C]; linarith) ha.1.le

end BianchiIX
