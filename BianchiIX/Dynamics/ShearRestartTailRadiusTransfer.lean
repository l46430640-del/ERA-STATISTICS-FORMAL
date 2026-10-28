import BianchiIX.Dynamics.ShearRestartTailRadius

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The full fixed-tail radius transfer, including the ordinary radial derivative, is quadratic in scale. -/
theorem exists_restartShearTail_radius_transfer :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let F := fun r => shearTailRadius (restartShearTailFlow h a q ζ ν T r) -
              shearTailRadius (restartShearTailFlow h a q ζ ν 0 r)
            DifferentiableAt ℝ F ρ ∧
            |F ρ| + a * |deriv F ρ| ≤ (1280 + 32768 * (105 + 40 * C * q + 20 * D)) * a ^ 2 := by
  obtain ⟨C, hC, hstar, hhstar, H⟩ := exists_restartShearTail_radius_rates
  refine ⟨C, hC, hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨astar, hastar, HA⟩ := H h hh q D P hq hD hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T F
  let α := fun t => restartShearTailFlow h a q ζ ν t ρ
  let v := fun t => restartShearTailRadialVariation h a q ζ ν t ρ
  let L₀ := shearTailLogSize (α 0) (v 0)
  let E := fun t => shearTailRadiusEnergy (α t)
  let I₀ := ∫ t in 0..T, E t
  let I₁ := ∫ t in 0..T, t * E t
  obtain ⟨hasmall, hT, HL₀, HE, HI₀, HI₁, HT⟩ := HA a ha ε ζ ν hε hζ hν ρ hρ
  have ha1 : a ≤ 1 := by linarith only [hasmall]
  have HC : 0 ≤ C := by linarith only [hC]
  have HQ : 0 ≤ q := by linarith only [hq]
  have HL₀0 : 0 ≤ L₀ := norm_nonneg _
  have hlog : a * |Real.log a| ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ha.1) ha.1.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ ha.1.ne'] at H
    rw [abs_of_nonpos (Real.log_nonpos ha.1.le ha1)]
    nlinarith only [H, ha.1]
  have HL : a * L₀ ≤ 2 + 4 * C * q := by
    have H := mul_le_mul_of_nonneg_left HL₀ ha.1.le
    have Hlog := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4 * C * q)
    nlinarith only [H, Hlog, ha1]
  have HI₁' : I₁ ≤ 4 + D := by
    have H := mul_le_mul_of_nonneg_left ha1 (by positivity : 0 ≤ 3 + D)
    linarith only [HI₁, H]
  have HB : (1 + 2 * a * L₀) * I₀ + 20 * a * I₁ ≤ (105 + 40 * C * q + 20 * D) * a := by
    have H0 := mul_le_mul_of_nonneg_left HI₀ (by positivity [ha.1] : 0 ≤ 1 + 2 * a * L₀)
    have H1 := mul_le_mul_of_nonneg_left HI₁' (by positivity [ha.1] : 0 ≤ 20 * a)
    have Hlog := mul_le_mul_of_nonneg_left HL (by positivity [ha.1] : 0 ≤ 10 * a)
    nlinarith only [H0, H1, Hlog]
  have HRtime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun u => shearTailRadius (α u)) (shearTailRadiusRate (α t)) t := (HT t ht).2.2.2.1
  have HV := abs_sub_le_integral_bound hT HRtime
    (show ContinuousOn (fun t => 256 * a * E t) (Icc (0 : ℝ) T) from continuousOn_const.mul HE)
    (fun t ht => (HT t ht).2.2.2.2.2.2.1)
  rw [intervalIntegral.integral_const_mul] at HV
  have HV' : |F ρ| ≤ 1280 * a ^ 2 := by
    have H0 := mul_le_mul_of_nonneg_left HI₀ (by positivity [ha.1] : 0 ≤ 256 * a)
    nlinarith only [HV, H0]
  have HRvar (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun u => deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν u r)) ρ)
        (shearTailRadiusRateDifferential (α t) (v t)) t := (HT t ht).2.2.2.2.2.1
  have Hcont : ContinuousOn (fun t => 32768 * E t * (1 + 2 * a * L₀ + 20 * a * t)) (Icc (0 : ℝ) T) := by
    fun_prop
  have HD := abs_sub_le_integral_bound hT HRvar Hcont (fun t ht => (HT t ht).2.2.2.2.2.2.2)
  have he (t : ℝ) : 32768 * E t * (1 + 2 * a * L₀ + 20 * a * t) =
      32768 * ((1 + 2 * a * L₀) * E t + (20 * a) * (t * E t)) := by ring
  simp_rw [he] at HD
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (f := fun t => (1 + 2 * a * L₀) * E t) (g := fun t => (20 * a) * (t * E t))
    ((continuousOn_const.mul HE).intervalIntegrable_of_Icc hT)
    ((continuousOn_const.mul (continuousOn_id.mul HE)).intervalIntegrable_of_Icc hT),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at HD
  have HD' : |deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν T r)) ρ -
      deriv (fun r => shearTailRadius (restartShearTailFlow h a q ζ ν 0 r)) ρ| ≤
      32768 * (105 + 40 * C * q + 20 * D) * a := by nlinarith only [HD, HB]
  have HR0 := (HT 0 ⟨le_rfl, hT⟩).2.2.1
  have HRT := (HT T ⟨hT, le_rfl⟩).2.2.1
  have HF : HasDerivAt F (shearTailRadiusDifferential (α T) (v T) -
      shearTailRadiusDifferential (α 0) (v 0)) ρ := HRT.sub HR0
  rw [HRT.deriv, HR0.deriv, ← HF.deriv] at HD'
  refine ⟨HF.differentiableAt, ?_⟩
  nlinarith only [HV', mul_le_mul_of_nonneg_left HD' ha.1.le]

end BianchiIX
