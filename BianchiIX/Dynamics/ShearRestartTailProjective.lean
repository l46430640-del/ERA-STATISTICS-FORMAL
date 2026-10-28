import BianchiIX.Dynamics.ShearRestartTailRadial
import BianchiIX.Dynamics.ShearTailWeightedEnergy
import BianchiIX.Dynamics.ShearTailProjectiveVariation

noncomputable section

namespace BianchiIX

open Set

/-- The exact radial family satisfies the weighted wall and projective log bounds on its full tail. -/
theorem exists_restartShearTail_projective_control :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let α := fun t => restartShearTailFlow h a q ζ ν t ρ
            let v := fun t => restartShearTailRadialVariation h a q ζ ν t ρ
            let L₀ := shearTailLogSize (α 0) (v 0)
            let K := 13 + 20 * C * q + D
            a ≤ 1 / 256 ∧ 0 ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) T,
              let w := shearTailProjectiveLogVariation (α t) (v t)
              (L₀ + t) * shearTailEnergy (α t) ≤ K * a ∧
              shearTailEnergy (α t) * shearTailLogSize (α t) (v t) ≤ 20 * K * a ∧
              HasDerivAt (fun r => shearTailProjectiveLogState (restartShearTailFlow h a q ζ ν t r)) w ρ ∧
              |w 0| + |w 1| ≤ (1000 + 2400 * K) / a ∧
              |w 2| + |w 3| + |w 4| ≤ (1000 + 2400 * K) * (1 / a + L₀ + t) ∧
              |deriv (fun r => projectiveCoord (restartShearTailFlow h a q ζ ν t r 0)
                (restartShearTailFlow h a q ζ ν t r 1)) ρ| ≤ 60 * (1000 + 2400 * K) / a ^ 2 := by
  obtain ⟨C, hC, hR, hhR, HR⟩ := exists_restartShearTail_radial_control
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨C, hC, min hR hV, lt_min hhR hhV, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aR, haR, HRa⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aV, haV, HVa⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aR aV, lt_min haR haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T α v L₀ K
  obtain ⟨hasmall, hT, HL₀, _, _, _, _, _, HRt⟩ :=
    HRa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, hrad, _, HT, _⟩ :=
    HVa a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have HC : 0 ≤ C := by linarith only [hC]
  have HQ : 0 ≤ q := by linarith only [hq]
  have HK : 0 ≤ K := by dsimp only [K]; positivity
  have HL₀0 : 0 ≤ L₀ := norm_nonneg _
  have Hcon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : stateConstraint (α t) = 1 := (HT t ht).2.2.1
  have Hnon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 := (HT t ht).2.2.2.1
  have Hreg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : shearTailRegion a (α t) := (HT t ht).2.2.2.2.1
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt α (normalizedField (α t)) t := by
    have H := (hasDerivAt_normalizedMaxCurve (HT t ht).1).scomp t
      ((hasDerivAt_id' t).add_const (q / 2 * Real.log (1 / a)))
    simpa only [Function.comp_def, one_smul, α, restartShearTailFlow] using H
  have HB := shearTail_prefix_weighted_energy ⟨ha.1, hasmall⟩ hD HC HQ ⟨HL₀0, HL₀⟩ HD Hcon Hnon Hreg
  refine ⟨hasmall, hT, ?_⟩
  intro t ht w
  obtain ⟨Hderiv, Hpos, HS, HL, _⟩ := HRt t ht
  have Hb0 : 0 ≤ shearTailEnergy (α t) := by
    dsimp only [shearTailEnergy]
    positivity [(Hnon t ht).1, (Hnon t ht).2.1, (Hnon t ht).2.2]
  have HBL : shearTailEnergy (α t) * shearTailLogSize (α t) (v t) ≤ 20 * K * a := by
    have H := mul_le_mul_of_nonneg_left HL Hb0
    have Hextra := mul_nonneg Hb0 HL₀0
    nlinarith only [H, HB t ht, Hextra]
  have Hv : normalizedConstraintDifferential (α t) (v t) = 0 := by
    have H := congrArg (fun L : NormalizedState →L[ℝ] ℝ => L (restartShearInitialVariation h ζ ν ρ))
      (normalizedConstraintDifferential_flow (HT t ht).1)
    simp only [ContinuousLinearMap.comp_apply] at H
    exact H.trans (restartShearInitialVariation_tangent hrad).2
  have HP := shearTail_projective_log_variation_bounds ⟨ha.1, hasmall⟩
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) HK) (Hcon t ht) (Hreg t ht) Hpos Hv HS HBL
  have HAl : a ^ 2 / 10 ≤ 1 + α t 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, HAl, _, _⟩ := HT t ht
    exact HAl
  have hA : 0 < 1 + α t 0 := (div_pos (sq_pos_of_pos ha.1) (by norm_num)).trans_le HAl
  have hs : 0 < α t 1 := by linarith only [(Hreg t ht).2.1, ha.1]
  have Hsum : |w 0| + |w 1| ≤ (1000 + 2400 * K) / a :=
    HP.1.trans ((div_le_div_iff_of_pos_right ha.1).mpr (by nlinarith only [HK]))
  refine ⟨HB t ht, HBL, hasDerivAt_shearTailProjectiveLogState Hderiv hA.ne' hs.ne'
    Hpos.1.ne' Hpos.2.1.ne' Hpos.2.2.ne', Hsum, ?_, ?_⟩
  · have Hfrac : (900 + 120 * (20 * K)) / a ≤ (1000 + 2400 * K) * (1 / a) := by
      rw [mul_one_div]
      exact (div_le_div_iff_of_pos_right ha.1).mpr (by linarith)
    calc
      _ ≤ 3 * shearTailLogSize (α t) (v t) + (900 + 120 * (20 * K)) / a := HP.2
      _ ≤ 6 * L₀ + 60 * t + (1000 + 2400 * K) * (1 / a) :=
        add_le_add (by linarith only [HL]) Hfrac
      _ ≤ _ := by nlinarith only [mul_nonneg HK HL₀0, mul_nonneg HK ht.1, HL₀0, ht.1]
  · exact (shearTail_projective_shear_response ha.1 Hderiv HAl ⟨hs, (Hreg t ht).2.2.1⟩
      (show |w 1| ≤ (1000 + 2400 * K) / a by linarith only [Hsum, abs_nonneg (w 0)])).2

end BianchiIX
