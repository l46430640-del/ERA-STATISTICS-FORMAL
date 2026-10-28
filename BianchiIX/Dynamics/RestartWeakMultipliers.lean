import BianchiIX.Dynamics.RestartSectionVariation
import BianchiIX.Analysis.RestartWeakBounds
import BianchiIX.Analysis.ScalarMultiplier
import BianchiIX.Analysis.CompactIntegralSecondRegularity

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def restartWeakRateIntegrand (i : Fin 2) (p : RestartState × ℝ) : ℝ :=
  restartMixedWeakRates (restartMixedFlow p) i

def restartWeakLogMultiplier (T : ℝ) (i : Fin 2) (y : RestartState) : ℝ :=
  ∫ t in 0..T, restartWeakRateIntegrand i (y, t)

def restartWeakMultiplier (T : ℝ) (i : Fin 2) (y : RestartState) : ℝ :=
  Real.exp (restartWeakLogMultiplier T i y)

theorem restartWeakMultiplier_pos (T : ℝ) (i : Fin 2) (y : RestartState) :
    0 < restartWeakMultiplier T i y := Real.exp_pos _

theorem restartWeakLogMultiplier_eq_log (T : ℝ) (i : Fin 2) (y : RestartState) :
    restartWeakLogMultiplier T i y = Real.log (restartWeakMultiplier T i y) :=
  (Real.log_exp _).symm

theorem contDiffAt_restartMixedWeakRates {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartMixedWeakRates y :=
  (contDiffAt_restartCompactWeakRates hy k).comp y (contDiff_restartExpCoordinates k).contDiffAt

theorem contDiffAt_restartWeakRateIntegrand {p : RestartState × ℝ}
    (H : restartMixedFlowRegular p) (i : Fin 2) :
    ContDiffAt ℝ 2 (restartWeakRateIntegrand i) p :=
  contDiffAt_pi.mp ((contDiffAt_restartMixedWeakRates (restartMixedFlow_radicand_pos H) 2).comp p
    (contDiffAt_restartMixedFlow_two H)) i

theorem hasDerivAt_restartMixedFlow_weak {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) (i : Fin 2) :
    HasDerivAt (fun s => restartMixedFlow (y, s) (i.addNat 2))
      (restartWeakRateIntegrand i (y, t) * restartMixedFlow (y, t) (i.addNat 2)) t := by
  have HD := (hasDerivAt_pi.mp (hasDerivAt_restartMixedFlow_time H)) (i.addNat 2)
  convert! HD using 1
  fin_cases i <;> simp [restartWeakRateIntegrand, restartMixedWeakRates, restartMixedField,
    Function.comp_apply, restartCompactField, restartCompactWeakRates, restartExpCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, mul_comm]

/-- The factors multiply the actual weak walls, including signed or zero initial amplitudes. -/
theorem restartWeakMultiplier_formula {y : RestartState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t)) (i : Fin 2) :
    restartMixedFlow (y, T) (i.addNat 2) = y (i.addNat 2) * restartWeakMultiplier T i y := by
  have hc : ContinuousOn (fun t => restartMixedFlow (y, t) (i.addNat 2)) (Icc (0 : ℝ) T) :=
    HasDerivAt.continuousOn (fun t ht => hasDerivAt_restartMixedFlow_weak (H t ht) i)
  have hr : ContinuousOn (fun t => restartWeakRateIntegrand i (y, t)) (Icc (0 : ℝ) T) :=
    fun t ht => ((contDiffAt_restartWeakRateIntegrand (H t ht) i).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have HF := homogeneous_solution_eq_exp_integral_Icc hT hr hc
    (fun t ht => hasDerivAt_restartMixedFlow_weak (H t (Ioo_subset_Icc_self ht)) i)
  simpa only [restartMixedFlow_initial, restartWeakMultiplier, restartWeakLogMultiplier] using HF

theorem restartWeakRateIntegrand_partial {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) (i : Fin 2) (v : RestartState) :
    fderiv ℝ (restartWeakRateIntegrand i) (y, t) (v, 0) =
      fderiv ℝ restartMixedWeakRates (restartMixedFlow (y, t))
        (fderiv ℝ (fun z => restartMixedFlow (z, t)) y v) i := by
  have HF := ((contDiffAt_restartMixedFlow_two H).comp y
    (contDiffAt_id.prodMk (contDiffAt_const (c := t)))).differentiableAt (by norm_num)
  have HG := (contDiffAt_restartMixedWeakRates (restartMixedFlow_radicand_pos H) 2).differentiableAt (by norm_num)
  have HA := (hasFDerivAt_pi'.mp HG.hasFDerivAt i).comp y HF.hasFDerivAt
  have HP := ((contDiffAt_restartWeakRateIntegrand H i).differentiableAt (by norm_num)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)
  exact congrArg (fun L : RestartState →L[ℝ] ℝ => L v) (HP.unique HA)

theorem restartWeakLogMultiplier_regular {y : RestartState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t)) (i : Fin 2) :
    ContDiffAt ℝ 1 (restartWeakLogMultiplier T i) y ∧
      fderiv ℝ (restartWeakLogMultiplier T i) y =
        ∫ t in 0..T, (fderiv ℝ (restartWeakRateIntegrand i) (y, t)).comp
          (ContinuousLinearMap.inl ℝ RestartState ℝ) := by
  have HG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ContDiffAt ℝ 1 (restartWeakRateIntegrand i) (y, t) :=
    (contDiffAt_restartWeakRateIntegrand (H t ht) i).of_le (by norm_num)
  exact ⟨contDiffAt_intervalIntegral_of_contDiffAt hT HG,
    (hasFDerivAt_intervalIntegral_of_contDiffAt hT HG).fderiv⟩

theorem contDiffAt_restartWeakLogMultiplier_two {y : RestartState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t)) (i : Fin 2) :
    ContDiffAt ℝ 2 (restartWeakLogMultiplier T i) y :=
  contDiffAt_intervalIntegral_two hT (fun t ht => contDiffAt_restartWeakRateIntegrand (H t ht) i)

theorem restartWeakLogMultiplier_derivative_bound {y : RestartState} {T C : ℝ}
    (hT : 0 ≤ T) (hC : 0 ≤ C)
    (H : ∀ t ∈ Icc (0 : ℝ) T, restartMixedFlowRegular (y, t))
    (HG : ∀ t ∈ Icc (0 : ℝ) T, ‖fderiv ℝ restartMixedWeakRates (restartMixedFlow (y, t))‖ ≤ C)
    (HF : ∀ t ∈ Icc (0 : ℝ) T, ‖fderiv ℝ (fun z => restartMixedFlow (z, t)) y‖ ≤ 2) (i : Fin 2) :
    ‖fderiv ℝ (restartWeakLogMultiplier T i) y‖ ≤ 2 * C * T := by
  rw [(restartWeakLogMultiplier_regular hT H i).2]
  have HI := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := T) (C := 2 * C)
    (f := fun t => (fderiv ℝ (restartWeakRateIntegrand i) (y, t)).comp
      (ContinuousLinearMap.inl ℝ RestartState ℝ)) ?_
  · simpa only [sub_zero, abs_of_nonneg hT] using HI
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := uIcc_of_le hT ▸ uIoc_subset_uIcc ht
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change |fderiv ℝ (restartWeakRateIntegrand i) (y, t) (v, 0)| ≤ _
    rw [restartWeakRateIntegrand_partial (H t ht') i v]
    have HV := ((fderiv ℝ (fun z => restartMixedFlow (z, t)) y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (HF t ht') (norm_nonneg v))
    have HR := (norm_le_pi_norm
      (fderiv ℝ restartMixedWeakRates (restartMixedFlow (y, t))
        (fderiv ℝ (fun z => restartMixedFlow (z, t)) y v)) i).trans
      (((fderiv ℝ restartMixedWeakRates (restartMixedFlow (y, t))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (HG t ht') (norm_nonneg _)))
    exact HR.trans (by nlinarith only [HV, hC])

end BianchiIX
