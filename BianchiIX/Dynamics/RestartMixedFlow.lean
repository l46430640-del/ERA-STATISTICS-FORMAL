import BianchiIX.Dynamics.RestartFastSection
import BianchiIX.Dynamics.FlowSecondRegularity
import BianchiIX.Dynamics.FlowTransport
import BianchiIX.Analysis.ParametricVariation
import BianchiIX.Analysis.ParameterSlice

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The negative constraint branch in four mixed coordinates. -/
def restartMixedChart (y : RestartState) : NormalizedState :=
  ![-restartCompactRoot (restartExpCoordinates y), y 1, Real.exp (y 0), y 2, y 3]

def restartMixedFlow (p : RestartState × ℝ) : RestartState :=
  restartMixedCoordinates (normalizedMaxCurve (restartMixedChart p.1) 0 p.2)

def restartMixedFlowRegular (p : RestartState × ℝ) : Prop :=
  0 < restartRadicand (restartExpCoordinates p.1) ∧
    p.2 ∈ normalizedMaxDomain (restartMixedChart p.1) 0 ∧
    normalizedMaxCurve (restartMixedChart p.1) 0 p.2 0 < 0 ∧
    0 < normalizedMaxCurve (restartMixedChart p.1) 0 p.2 2

theorem restartMixedChart_constraint {y : RestartState}
    (hy : 0 ≤ restartRadicand (restartExpCoordinates y)) :
    stateConstraint (restartMixedChart y) = 1 := by
  have H := Real.sq_sqrt hy
  dsimp [stateConstraint, constraint, shearSq, restartMixedChart, restartCompactRoot]
  rw [neg_sq, H]
  dsimp [restartRadicand, restartExpCoordinates]
  ring

theorem restartMixedCoordinates_chart (y : RestartState) :
    restartMixedCoordinates (restartMixedChart y) = y := by
  ext i
  fin_cases i <;> simp [restartMixedCoordinates, restartMixedChart, Real.log_exp]

theorem restartExpCoordinates_mixed {x : NormalizedState} (hn : 0 < x 2) :
    restartExpCoordinates (restartMixedCoordinates x) = restartPhysicalCoordinates x := by
  ext i
  fin_cases i <;> simp [restartExpCoordinates, restartMixedCoordinates,
    restartPhysicalCoordinates, Real.exp_log hn]

theorem restartMixedFlow_initial (y : RestartState) : restartMixedFlow (y, 0) = y := by
  rw [restartMixedFlow, normalizedMaxCurve_initial, restartMixedCoordinates_chart]

theorem contDiffAt_restartMixedChart {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartMixedChart y := by
  have hr := (contDiffAt_restartCompactRoot hy k).comp y (contDiff_restartExpCoordinates k).contDiffAt
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact hr.neg
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 4) y
  · exact (contDiffAt_apply ℝ ℝ (0 : Fin 4) y).exp
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 4) y
  · exact contDiffAt_apply ℝ ℝ (3 : Fin 4) y

theorem contDiffAt_restartMixedCoordinates {x : NormalizedState} (hn : x 2 ≠ 0)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartMixedCoordinates x := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (contDiffAt_apply ℝ ℝ (2 : Fin 5) x).log hn
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 5) x
  · exact contDiffAt_apply ℝ ℝ (3 : Fin 5) x
  · exact contDiffAt_apply ℝ ℝ (4 : Fin 5) x

theorem contDiffAt_restartMixedFlow_two {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    ContDiffAt ℝ 2 restartMixedFlow p := by
  have hc := (contDiffAt_restartMixedChart hp.1 2).comp p contDiffAt_fst
  have hf := (contDiffAt_normalizedMaxCurve_two hp.2.1).comp p (hc.prodMk contDiffAt_snd)
  exact (contDiffAt_restartMixedCoordinates hp.2.2.2.ne' 2).comp p hf

theorem restartMixedFlowRegular_eventually {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    ∀ᶠ q in 𝓝 p, restartMixedFlowRegular q := by
  have hr : ContinuousAt (fun q : RestartState × ℝ => restartRadicand (restartExpCoordinates q.1)) p :=
    ((contDiff_restartRadicand 0).continuous.comp (contDiff_restartExpCoordinates 0).continuous).continuousAt.comp
      continuousAt_fst
  have hc := (contDiffAt_restartMixedChart hp.1 2).comp p contDiffAt_fst
  have he := hc.continuousAt.prodMk continuousAt_snd
  have hf := (contDiffAt_normalizedMaxCurve_two hp.2.1).comp p (hc.prodMk contDiffAt_snd)
  have hpcont := (continuous_apply (0 : Fin 5)).continuousAt.comp hf.continuousAt
  have hncont := (continuous_apply (2 : Fin 5)).continuousAt.comp hf.continuousAt
  filter_upwards [hr.eventually (isOpen_Ioi.mem_nhds hp.1),
    he.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hp.2.1),
    hpcont.eventually (isOpen_Iio.mem_nhds hp.2.2.1),
    hncont.eventually (isOpen_Ioi.mem_nhds hp.2.2.2)] with q hqr hqd hqp hqn
  exact ⟨hqr, hqd, hqp, hqn⟩

theorem hasDerivAt_restartMixedFlow_time {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) :
    HasDerivAt (fun s => restartMixedFlow (y, s)) (restartMixedField (restartMixedFlow (y, t))) t :=
  hasDerivAt_restartMixedCoordinates (hasDerivAt_normalizedMaxCurve H.2.1)
    ((normalizedMaxCurve_constraint H.2.1).trans (restartMixedChart_constraint H.1.le)) H.2.2.1 H.2.2.2

theorem restartMixedFlow_local_partial_time {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    (fun q => fderiv ℝ restartMixedFlow q (0, 1)) =ᶠ[𝓝 p]
      (fun q => restartMixedField (restartMixedFlow q)) := by
  filter_upwards [restartMixedFlowRegular_eventually hp] with q hq
  have hpath : HasDerivAt (fun s : ℝ => (q.1, s)) (0, 1) q.2 :=
    (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
  have HD := ((contDiffAt_restartMixedFlow_two hq).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    (f := fun s : ℝ => (q.1, s)) q.2 hpath
  exact HD.unique (hasDerivAt_restartMixedFlow_time hq)

theorem restartMixedFlow_radicand_pos {p : RestartState × ℝ} (hp : restartMixedFlowRegular p) :
    0 < restartRadicand (restartExpCoordinates (restartMixedFlow p)) := by
  have hc := (normalizedMaxCurve_constraint hp.2.1).trans (restartMixedChart_constraint hp.1.le)
  have H : restartRadicand (restartPhysicalCoordinates (normalizedMaxCurve (restartMixedChart p.1) 0 p.2)) =
      (normalizedMaxCurve (restartMixedChart p.1) 0 p.2 0) ^ 2 := by
    dsimp [stateConstraint, constraint, shearSq] at hc
    dsimp [restartRadicand, restartPhysicalCoordinates]
    linarith only [hc]
  dsimp only [restartMixedFlow]
  rw [restartExpCoordinates_mixed hp.2.2.2, H]
  exact sq_pos_of_neg hp.2.2.1

/-- The genuine initial-coordinate derivative satisfies the reduced variational equation. -/
theorem hasDerivAt_restartMixedFlow_variation {y : RestartState} {t : ℝ}
    (H : restartMixedFlowRegular (y, t)) (v : RestartState) :
    HasDerivAt (fun s => fderiv ℝ restartMixedFlow (y, s) (v, 0))
      (fderiv ℝ restartMixedField (restartMixedFlow (y, t))
        (fderiv ℝ restartMixedFlow (y, t) (v, 0))) t := by
  have hf : DifferentiableAt ℝ (fun p : ℝ × RestartState => restartMixedField p.2)
      (t, restartMixedFlow (y, t)) :=
    ((contDiffAt_restartMixedField (restartMixedFlow_radicand_pos H) 1).comp
      (t, restartMixedFlow (y, t)) contDiffAt_snd).differentiableAt (by norm_num)
  exact hasDerivAt_parametric_first_variation (contDiffAt_restartMixedFlow_two H) hf
    (restartMixedFlow_local_partial_time H) v

theorem restartMixedFlow_variation_initial {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (v : RestartState) :
    fderiv ℝ restartMixedFlow (y, 0) (v, 0) = v := by
  have H : restartMixedFlowRegular (y, 0) := by
    refine ⟨hy, initial_mem_normalizedMaxDomain _ _, ?_, ?_⟩
    · rw [normalizedMaxCurve_initial]
      exact neg_lt_zero.mpr (Real.sqrt_pos.mpr hy)
    · rw [normalizedMaxCurve_initial]
      exact Real.exp_pos _
  rw [← fderiv_parameterSlice_apply ((contDiffAt_restartMixedFlow_two H).differentiableAt (by norm_num)) v]
  simp only [restartMixedFlow_initial, fderiv_fun_id, ContinuousLinearMap.id_apply]

end BianchiIX
