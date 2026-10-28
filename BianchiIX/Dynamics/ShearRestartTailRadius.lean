import BianchiIX.Dynamics.ShearRestartTailRadial
import BianchiIX.Dynamics.ShearTailRadiusRateBounds
import BianchiIX.Dynamics.ShearTailRadiusMoments
import BianchiIX.Analysis.PartialDerivativeTime

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

/-- Joint regularity identifies the time derivative of the actual radial response with the rate response. -/
theorem hasDerivAt_restartShearTailRadius_variation {h a q ζ ν t ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ))
    (ht : t + q / 2 * Real.log (1 / a) ∈
      normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0)
    (hs : restartShearTailFlow h a q ζ ν t ρ 1 ≠ 0) :
    HasDerivAt (fun u => deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν u r)) ρ)
      (shearTailRadiusRateDifferential (restartShearTailFlow h a q ζ ν t ρ)
        (restartShearTailRadialVariation h a q ζ ν t ρ)) t := by
  let t₀ := q / 2 * Real.log (1 / a)
  let X : ℝ × ℝ → NormalizedState := fun p => restartShearTailFlow h a q ζ ν p.2 p.1
  let Φ : ℝ × ℝ → ℝ := fun p => shearTailRadius (X p)
  let G : ℝ × ℝ → ℝ := fun p => shearTailRadiusRate (X p)
  have HC : ContDiff ℝ 2 (restartShearCurve 1 ζ ν) := by
    rw [contDiff_pi]
    intro i
    fin_cases i <;> dsimp [restartShearCurve] <;> fun_prop
  have Hchart := (contDiffAt_restartSectionChart hrad 2).comp (ρ, t)
    (HC.contDiffAt.comp (ρ, t) contDiffAt_fst)
  have Hclock : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.2 + t₀) (ρ, t) := by fun_prop
  have HI := Hchart.prodMk Hclock
  have HX : ContDiffAt ℝ 2 X (ρ, t) := (contDiffAt_normalizedMaxCurve_two ht).comp (ρ, t)
    (g := fun y : NormalizedState × ℝ => normalizedMaxCurve y.1 0 y.2) HI
  have HΦ : ContDiffAt ℝ 2 Φ (ρ, t) :=
    (contDiffAt_shearTailRadius hs 2).comp (ρ, t) (g := shearTailRadius) HX
  have Hrad : Continuous (fun p : ℝ × ℝ => restartSectionRadicand h (restartShearCurve 1 ζ ν p.1)) := by
    unfold restartSectionRadicand restartShearCurve curvature
    fun_prop
  have Htime : (fun p => fderiv ℝ Φ p (0, 1)) =ᶠ[𝓝 (ρ, t)] G := by
    filter_upwards [Hrad.continuousAt.eventually (isOpen_Ioi.mem_nhds hrad),
      HI.continuousAt.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds ht),
      ((continuous_apply 1).continuousAt.comp HX.continuousAt).eventually_ne hs,
      HΦ.eventually (by norm_num)] with p hp ht' hs' hΦ
    have HD : HasDerivAt (fun u => X (p.1, u)) (normalizedField (X p)) p.2 := by
      have H := (hasDerivAt_normalizedMaxCurve ht').scomp p.2 ((hasDerivAt_id' p.2).add_const t₀)
      simpa only [Function.comp_def, one_smul, X, restartShearTailFlow, t₀] using H
    have Hcon : stateConstraint (X p) = 1 :=
      (normalizedMaxCurve_constraint ht').trans (restartSectionChart_constraint hp.le)
    have HR := hasDerivAt_shearTailRadius_time HD Hcon hs'
    have HP := (hΦ.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2))
    exact HP.unique HR
  have HM := hasDerivAt_parameter_fderiv_of_local_time HΦ Htime (1 : ℝ)
  have HR := hasDerivAt_shearTailRadiusRate (hasDerivAt_restartShearTailFlow hrad ht) hs
  change HasDerivAt (fun u => deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν u r)) ρ)
    (deriv (fun r => shearTailRadiusRate (restartShearTailFlow h a q ζ ν t r)) ρ) t at HM
  rwa [HR.deriv] at HM

/-- All radius and rate derivatives are ordinary derivatives of one exact fast-layer and tail family. -/
theorem exists_restartShearTail_radius_rates :
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
            a ≤ 1 / 256 ∧ 0 ≤ T ∧ L₀ ≤ 2 + 4 * C * q * |Real.log a| ∧
            ContinuousOn (fun t => shearTailRadiusEnergy (α t)) (Icc (0 : ℝ) T) ∧
            (∫ t in 0..T, shearTailRadiusEnergy (α t)) ≤ 5 * a ∧
            (∫ t in 0..T, t * shearTailRadiusEnergy (α t)) ≤ 1 / 256 + (3 + D) * a ∧
            ∀ t ∈ Icc (0 : ℝ) T,
              a / 2 ≤ shearTailRadius (α t) ∧ shearTailRadius (α t) ≤ 4 * a ∧
              HasDerivAt (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν t r))
                (shearTailRadiusDifferential (α t) (v t)) ρ ∧
              HasDerivAt (fun u => shearTailRadius (α u)) (shearTailRadiusRate (α t)) t ∧
              HasDerivAt (fun r => shearTailRadiusRate (restartShearTailFlow h a q ζ ν t r))
                (shearTailRadiusRateDifferential (α t) (v t)) ρ ∧
              HasDerivAt (fun u => deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν u r)) ρ)
                (shearTailRadiusRateDifferential (α t) (v t)) t ∧
              |shearTailRadiusRate (α t)| ≤ 256 * a * shearTailRadiusEnergy (α t) ∧
              |shearTailRadiusRateDifferential (α t) (v t)| ≤
                32768 * shearTailRadiusEnergy (α t) * (1 + 2 * a * L₀ + 20 * a * t) := by
  obtain ⟨C, hC, hR, hhR, HR⟩ := exists_restartShearTail_radial_control
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨C, hC, min hR hV, lt_min hhR hhV, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aR, haR, HRa⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aV, haV, HVa⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P hq hD hP
  refine ⟨min aR aV, lt_min haR haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T α v L₀
  obtain ⟨hasmall, hT, HL₀, HJ₀, HJ₁, _, _, _, HRt⟩ :=
    HRa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, hrad, _, HT, _⟩ :=
    HVa a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have Hα (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt α (normalizedField (α t)) t := by
    have H := (hasDerivAt_normalizedMaxCurve (HT t ht).1).scomp t
      ((hasDerivAt_id' t).add_const (q / 2 * Real.log (1 / a)))
    simpa only [Function.comp_def, one_smul, α, restartShearTailFlow] using H
  have HM := shearTail_prefix_radius_moments ⟨ha.1, hasmall⟩ hT Hα
    (fun t ht => (HT t ht).2.2.1) (fun t ht => (HT t ht).2.2.2.1)
    (fun t ht => (HT t ht).2.2.2.2.1)
  have Hcont := HasDerivAt.continuousOn Hα
  have HEcont : ContinuousOn (fun t => shearTailRadiusEnergy (α t)) (Icc (0 : ℝ) T) := by
    unfold shearTailRadiusEnergy
    fun_prop
  have Hreg₀ : shearTailRegion a (α 0) := (HT 0 ⟨le_rfl, hT⟩).2.2.2.2.1
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, hasmall]
  have HI₀ : (∫ t in 0..T, shearTailRadiusEnergy (α t)) ≤ 5 * a := by
    linarith only [HM.1, HJ₀, Hreg₀.2.2.2.1, ha2, ha.1]
  have HI₁ : (∫ t in 0..T, t * shearTailRadiusEnergy (α t)) ≤ 1 / 256 + (3 + D) * a := by
    nlinarith only [HM.2, HJ₁, Hreg₀.2.2.2.1, ha2, ha.1]
  refine ⟨hasmall, hT, HL₀, HEcont, HI₀, HI₁, ?_⟩
  intro t ht
  obtain ⟨Hderiv, Hpos, HS, HL, _⟩ := HRt t ht
  have Hcon : stateConstraint (α t) = 1 := (HT t ht).2.2.1
  have Hnon : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 := (HT t ht).2.2.2.1
  have Hreg : shearTailRegion a (α t) := (HT t ht).2.2.2.2.1
  have hs : α t 1 ≠ 0 := ne_of_gt (by linarith only [Hreg.2.1, ha.1])
  have Hbounds := shearTailRadius_region_bounds ⟨ha.1, by linarith only [hasmall]⟩ Hreg Hnon.2
  have HD := Hα t ht
  have Hv : normalizedConstraintDifferential (α t) (v t) = 0 := by
    have H := congrArg (fun L : NormalizedState →L[ℝ] ℝ => L (restartShearInitialVariation h ζ ν ρ))
      (normalizedConstraintDifferential_flow (HT t ht).1)
    simp only [ContinuousLinearMap.comp_apply] at H
    exact H.trans (restartShearInitialVariation_tangent hrad).2
  have HW (i : Fin 3) (hi : 0 < α t (i.addNat 2)) :
      |v t (i.addNat 2)| ≤ α t (i.addNat 2) * shearTailLogSize (α t) (v t) := by
    have H := norm_le_pi_norm (fun j : Fin 3 => v t (j.addNat 2) / α t (j.addNat 2)) i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hi] at H
    simpa only [shearTailLogSize, mul_comm] using (div_le_iff₀ hi).mp H
  have HB := shearTailRadius_rate_bounds ⟨ha.1, hasmall⟩ (norm_nonneg _) Hcon Hreg Hnon Hv HS
    ⟨HW 0 Hpos.1, HW 1 Hpos.2.1, HW 2 Hpos.2.2⟩
  refine ⟨Hbounds.1, Hbounds.2, hasDerivAt_shearTailRadius Hderiv hs,
    hasDerivAt_shearTailRadius_time HD Hcon hs, hasDerivAt_shearTailRadiusRate Hderiv hs,
    hasDerivAt_restartShearTailRadius_variation hrad (HT t ht).1 hs, HB.1, ?_⟩
  have HE : 0 ≤ shearTailRadiusEnergy (α t) := by dsimp only [shearTailRadiusEnergy]; positivity [Hnon.1]
  have H := mul_le_mul_of_nonneg_left HL
    (by positivity [ha.1] : 0 ≤ 32768 * a * shearTailRadiusEnergy (α t))
  have Hrate : |shearTailRadiusRateDifferential (α t) (v t)| ≤
      32768 * shearTailRadiusEnergy (α t) * (1 + a * shearTailLogSize (α t) (v t)) := HB.2
  nlinarith only [Hrate, H]

end BianchiIX
