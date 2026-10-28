import BianchiIX.Analysis.ShearTailVariationBudget
import BianchiIX.Dynamics.ShearTailInitialVariation
import BianchiIX.Dynamics.ShearTailIntegratedVariation
import BianchiIX.Dynamics.ShearTailMomentScale

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- One scale proves all moment budgets and the actual radial bounds throughout the joined tail. -/
theorem exists_restartShearTail_radial_control :
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
            let J₀ := ∫ t in 0..T, shearTailEnergy (α t)
            let J₁ := ∫ t in 0..T, t * shearTailEnergy (α t)
            a ≤ 1 / 256 ∧ 0 ≤ T ∧ L₀ ≤ 2 + 4 * C * q * |Real.log a| ∧
            J₀ ≤ 4 * a ∧ J₁ ≤ 1 / 256 + (2 + D) * a ∧
            9 * J₀ ≤ Real.log 2 ∧ 2 * J₀ + 16 * J₁ ≤ 1 / 2 ∧ L₀ * J₀ ≤ 1 / 16 ∧
            ∀ t ∈ Icc (0 : ℝ) T,
              HasDerivAt (restartShearTailFlow h a q ζ ν t) (v t) ρ ∧ positiveWalls (α t) ∧
              |v t 1| ≤ 5 ∧ shearTailLogSize (α t) (v t) ≤ 2 * L₀ + 20 * t ∧
              shearTailLogSize (α t) (v t) ≤ 4 + 8 * C * q * |Real.log a| + 20 * t := by
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  obtain ⟨C, hC, hI, hhI, HI⟩ := exists_restartShearTail_initial_variation
  refine ⟨C, hC, min hV hI, lt_min hhV hhI, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aV, haV, HVa⟩ := HV h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aI, haI, HIa⟩ := HI h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q hq
  obtain ⟨aB, haB, HBa⟩ := exists_shearTail_variation_budget
    (le_trans (by norm_num : (0 : ℝ) ≤ 32) hC) hq hP
  refine ⟨min aV (min aI aB), lt_min haV (lt_min haI haB), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T α v L₀ J₀ J₁
  let t₀ := q / 2 * Real.log (1 / a)
  let x := restartSectionChart h (restartShearCurve 1 ζ ν ρ)
  obtain ⟨_, ht₀, hT, hrad, hcx, HT, _⟩ := HVa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, by linarith only [hε.2]⟩
  obtain ⟨_, _, _, _, Hs₀, HL₀⟩ := HIa a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε'
    ⟨hζ.1, hζ.2.2⟩ hν ρ hρ
  obtain ⟨hasmall, hpow, HB⟩ := HBa a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hdom (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : t + t₀ ∈ normalizedMaxDomain x 0 := (HT t ht).1
  have Hcon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : stateConstraint (α t) = 1 := (HT t ht).2.2.1
  have Hnon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 := (HT t ht).2.2.2.1
  have Hreg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : shearTailRegion a (α t) := (HT t ht).2.2.2.2.1
  have Hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : positiveWalls (α t) :=
    (normalizedMaxCurve_forward (show positiveWalls x from ⟨hh.1, hζ.1, hν.1⟩) hcx
      (add_nonneg ht.1 ht₀)).2.1
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt α (normalizedField (α t)) t := by
    have H := (hasDerivAt_normalizedMaxCurve (Hdom t ht)).scomp t ((hasDerivAt_id' t).add_const t₀)
    simpa only [Function.comp_def, one_smul, α, restartShearTailFlow, x, t₀] using H
  have Hgrow : α 0 3 * Real.exp (6 * a * T) ≤ a ^ 2 := by
    obtain ⟨_, _, _, _, _, _, Hx, _⟩ := HT 0 ⟨le_rfl, hT⟩
    simp only [mul_zero, Real.exp_zero, mul_one] at Hx
    change α 0 3 ≤ 2 * ζ at Hx
    change α 0 3 * Real.exp (6 * a * shearTailTime a D) ≤ a ^ 2
    rw [exp_shearTailTime ha.1 6 D]
    have Hid : a ^ P * a ^ (-6 * D) = a ^ (P - 6 * D - 2) * a ^ 2 := by
      rw [← Real.rpow_two a, ← Real.rpow_add ha.1, ← Real.rpow_add ha.1]
      congr 1
      ring
    calc
      _ ≤ (2 * a ^ P) * a ^ (-6 * D) := mul_le_mul_of_nonneg_right
        (Hx.trans (mul_le_mul_of_nonneg_left hζ.2.1 (by norm_num))) (Real.rpow_nonneg ha.1.le _)
      _ = (2 * a ^ (P - 6 * D - 2)) * a ^ 2 := by rw [mul_assoc, Hid]; ring
      _ ≤ a ^ 2 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (sq_nonneg a)
  have HM := shearTail_prefix_moments_linear ⟨ha.1, hasmall⟩ hD HD Hcon Hnon Hreg Hgrow
  have Hb0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ shearTailEnergy (α t) := by
    dsimp only [shearTailEnergy]
    positivity [(Hnon t ht).1, (Hnon t ht).2.1, (Hnon t ht).2.2]
  have HJ₀ : 0 ≤ J₀ := intervalIntegral.integral_nonneg hT Hb0
  obtain ⟨HB0, HB1, HBL⟩ := HB L₀ J₀ J₁ HL₀ HJ₀ HM.1 HM.2
  have Hregion (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 ≤ -(15 / 16) ∧ |α t 1| ≤ 1 / 8 := by
    obtain ⟨hp, hsl, hsu, hn, hx, hy⟩ := Hreg t ht
    obtain ⟨_, _, _, _, Hpp, _, _⟩ := shearTail_constraint_bounds ⟨ha.1, hasmall⟩
      (by linarith only [hp]) ⟨hsl, hsu⟩ ⟨(Hnon t ht).1, hn⟩ ⟨(Hnon t ht).2.1, hx⟩
      ⟨(Hnon t ht).2.2, hy⟩ (Hcon t ht)
    exact ⟨Hpp, abs_le.mpr ⟨by linarith only [hsl, ha.1], by linarith only [hsu, hasmall]⟩⟩
  have HVeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := restartShearTail_radial_equation hrad
    (Hdom t ht) (Hregion t ht).1 (Hregion t ht).2 (Hpos t ht)
  let S : ℝ → ℝ := fun t => v t 1
  let L : ℝ → (Fin 3 → ℝ) := fun t i => shearTailVariation (α t) (v t) i.succ
  let S' : ℝ → ℝ := fun t => shearTailVariationRate (α t) (v t) 0
  let L' : ℝ → (Fin 3 → ℝ) := fun t i => shearTailVariationRate (α t) (v t) i.succ
  have HE (t : ℝ) : shearTailLogSize (α t) (v t) = ‖L t‖ := shearTailLogSize_eq_norm_variation _ _
  have HS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt S (S' t) t := hasDerivAt_pi.mp (HVeq t ht).1 0
  have HL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt L (L' t) t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mp (HVeq t ht).1 i.succ)
  have Hα := HasDerivAt.continuousOn HD
  have Hb : ContinuousOn (fun t => shearTailEnergy (α t)) (Icc (0 : ℝ) T) := by unfold shearTailEnergy; fun_prop
  have HSb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |S' t| ≤ 2 * shearTailEnergy (α t) * |S t| + 4 * shearTailEnergy (α t) * ‖L t‖ := by
    simpa only [← HE t] using (HVeq t ht).2.1
  have HLb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖L' t‖ ≤ 2 * |S t| + 9 * shearTailEnergy (α t) * ‖L t‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity [Hb0 t ht])).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← HE t] using (HVeq t ht).2.2 i
  have Hvariation := two_moment_variation_small hT HS HL Hb Hb0 HSb HLb Hs₀
    ⟨HB0, HB1, by simpa only [← HE 0] using HBL⟩
  refine ⟨hasmall, hT, HL₀, HM.1, HM.2, HB0, HB1, HBL, ?_⟩
  intro t ht
  have Hlog : shearTailLogSize (α t) (v t) ≤ 2 * L₀ + 20 * t := by
    simpa only [← HE] using (Hvariation t ht).2
  exact ⟨hasDerivAt_restartShearTailFlow hrad (Hdom t ht), Hpos t ht,
    (Hvariation t ht).1, Hlog, by linarith only [Hlog, HL₀]⟩

end BianchiIX
