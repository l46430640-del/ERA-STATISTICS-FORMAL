import BianchiIX.Dynamics.TransverseWallArrival
import BianchiIX.Dynamics.SmoothEventBranch
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology ContDiff

/-- An actual wall crossing from any smooth transverse chart has smooth time and a smooth
local inverse, including crossings at zero or negative elapsed time. -/
theorem exists_transverse_axisWall_smooth_arrival (A : NormalizedSymmetry)
    {C : SectionCoordinates → NormalizedState} {S : Set SectionCoordinates}
    {y : SectionCoordinates} {t₀ t h : ℝ} (hS : IsOpen S) (hy : y ∈ S)
    (hC : ContDiffOn ℝ ∞ C S) (hp : ∀ v ∈ S, positiveWalls (C v))
    (hc : ∀ v ∈ S, stateConstraint (C v) = 1)
    (hflux : ∀ v ∈ S,
      normalizedSectionFlux (C v) (fun i => fderiv ℝ C v (Pi.single i 1)) ≠ 0)
    (ht : t ∈ normalizedMaxDomain (C y) t₀) (hh : 0 < h)
    (hlevel : A.map (normalizedMaxCurve (C y) t₀ t) 2 = h)
    (hneg : A.map (normalizedMaxCurve (C y) t₀ t) 0 < 0) :
    ∃ τ : SectionCoordinates → ℝ,
      ∃ e : OpenPartialHomeomorph SectionCoordinates SectionCoordinates,
        y ∈ e.source ∧ e.source ⊆ S ∧ τ y = t ∧
        ContDiffOn ℝ ∞ τ e.source ∧ ContDiffOn ℝ ∞ e e.source ∧
        ContDiffOn ℝ ∞ e.symm e.target ∧
        (∀ v ∈ e.source, τ v ∈ normalizedMaxDomain (C v) t₀ ∧
          e v ∈ mainWallChartDomain h ∧
          axisWallChart A h (e v) = normalizedMaxCurve (C v) t₀ (τ v)) ∧
        (∀ᶠ p : SectionCoordinates × ℝ in 𝓝 (y, t), p.1 ∈ e.source ∧
          p.2 ∈ normalizedMaxDomain (C p.1) t₀ ∧
          (A.map (normalizedMaxCurve (C p.1) t₀ p.2) 2 = h ↔ τ p.1 = p.2)) := by
  have hCy : ContDiffAt ℝ ∞ C y := (hC y hy).contDiffAt (hS.mem_nhds hy)
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcMap⟩ :=
    exists_normalized_axisWall_event A ht hh hlevel hneg
  let T := fun v => τ (C v)
  let F := fun v => normalizedMaxCurve (C v) t₀ (T v)
  let R := fun v => axisWallCoordinates A (F v)
  have hF : ContDiffAt ℝ 1 F y := hcMap.comp y (hCy.of_le (by simp))
  have hFy : F y = normalizedMaxCurve (C y) t₀ t := by simp only [F, T, hτ]
  have hpF : positiveWalls (F y) := by
    rw [hFy]
    exact ((maximalNormalizedSolution (C y) t₀).physical (hp y hy) (hc y hy) ht).1
  have hpos : ∀ᶠ v in 𝓝 y, positiveWalls (F v) :=
    hF.continuousAt.eventually (isOpen_positiveWalls.mem_nhds hpF)
  have hnegative : ∀ᶠ v in 𝓝 y, A.map (F v) 0 < 0 := by
    have H : ContinuousAt (fun v => A.map (F v) 0) y := by fun_prop
    exact H.eventually_lt continuousAt_const (by rw [hFy]; exact hneg)
  have hgood := (show ∀ᶠ v in 𝓝 y, v ∈ S from hS.mem_nhds hy).and
    ((hCy.continuousAt.eventually (hcτ.eventually (by simp))).and
      ((hCy.continuousAt.eventually hhit).and (hpos.and hnegative)))
  obtain ⟨U, hU, hUo, hyU⟩ := mem_nhds_iff.mp hgood
  have hlocal (v : SectionCoordinates) (hv : v ∈ U) :
      R v ∈ mainWallChartDomain h ∧ axisWallChart A h (R v) = F v :=
    axisWallChart_coordinates A (hU hv).2.2.2.1
      ((normalizedMaxCurve_constraint (hU hv).2.2.1.1).trans (hc v (hU hv).1))
      (hU hv).2.2.2.2 (hU hv).2.2.1.2
  have hsmooth (v : SectionCoordinates) (hv : v ∈ U) :
      ContDiffAt ℝ ∞ T v ∧ ContDiffAt ℝ ∞ R v := by
    have hCv : ContDiffAt ℝ ∞ C v := (hC v (hU hv).1).contDiffAt (hS.mem_nhds (hU hv).1)
    have hg : ContDiffAt ℝ ∞ (fun x : NormalizedState => A.map x 2) (F v) := by fun_prop
    have htrans : normalizedEventRate (fun x => A.map x 2) (C v) t₀ (T v) ≠ 0 := by
      rw [normalizedEventRate_axisWall, (hU hv).2.2.1.2]
      have hr : rateOne (A.map (F v) 0) (A.map (F v) 1) < 0 := by
        unfold rateOne shearSq
        nlinarith [sq_nonneg (A.map (F v) 0), sq_nonneg (A.map (F v) 1), (hU hv).2.2.2.2]
      exact ne_of_lt (mul_neg_of_neg_of_pos hr hh)
    have hevent : ∀ᶠ w in 𝓝 v, A.map (F w) 2 = A.map (F v) 2 := by
      filter_upwards [hUo.mem_nhds hv] with w hw
      exact (hU hw).2.2.1.2.trans (hU hv).2.2.1.2.symm
    obtain ⟨hT, hFs⟩ := contDiffAt_normalized_event_branch hCv (hU hv).2.2.1.1 hg htrans
      ((hU hv).2.1.continuousAt.comp hCv.continuousAt) hevent
    exact ⟨hT, (contDiffAt_axisWallCoordinates A (hU hv).2.2.2.1 ∞).comp v
      (g := axisWallCoordinates A) (f := F) hFs⟩
  have hdet (v : SectionCoordinates) (hv : v ∈ U) : (fderiv ℝ R v).det ≠ 0 := by
    have hCv := (hC v (hU hv).1).contDiffAt (hS.mem_nhds (hU hv).1)
    have hconstraint : ∀ᶠ w in 𝓝 v, stateConstraint (C w) = 1 :=
      (show ∀ᶠ w in 𝓝 v, w ∈ S from hS.mem_nhds (hU hv).1).mono fun w hw => hc w hw
    have heq : (fun w => axisWallChart A h (R w)) =ᶠ[𝓝 v] F :=
      (show ∀ᶠ w in 𝓝 v, w ∈ U from hUo.mem_nhds hv).mono fun w hw => (hlocal w hw).2
    exact normalized_chart_arrival_det_ne_zero (hCv.differentiableAt (by simp))
      ((contDiffAt_axisWallChart A (hlocal v hv).1 ∞).differentiableAt (by simp))
      ((hsmooth v hv).2.differentiableAt (by simp)) ((hU hv).2.1.differentiableAt (by norm_num))
      (hp v (hU hv).1) hconstraint (hU hv).2.2.1.1 (hflux v (hU hv).1) heq
  have hd (v : SectionCoordinates) (hv : v ∈ U) :
      ∃ L : SectionCoordinates ≃L[ℝ] SectionCoordinates,
        HasFDerivAt R (L : SectionCoordinates →L[ℝ] SectionCoordinates) v := by
    let L := (fderiv ℝ R v).toContinuousLinearEquivOfDetNeZero (hdet v hv)
    refine ⟨L, ?_⟩
    rw [show (L : SectionCoordinates →L[ℝ] SectionCoordinates) = fderiv ℝ R v from
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _]
    exact ((hsmooth v hv).2.differentiableAt (by simp)).hasFDerivAt
  obtain ⟨L, hL⟩ := hd y hyU
  let e₀ := (hsmooth y hyU).2.toOpenPartialHomeomorph R hL (by simp)
  have hye₀ : y ∈ e₀.source := (hsmooth y hyU).2.mem_toOpenPartialHomeomorph_source hL (by simp)
  let e := e₀.restrOpen U hUo
  have hes (v : SectionCoordinates) (hv : v ∈ e.source) : v ∈ U := hv.2
  have hye : y ∈ e.source := ⟨hye₀, hyU⟩
  refine ⟨T, e, hye, fun v hv => (hU (hes v hv)).1, hτ,
    fun v hv => (hsmooth v (hes v hv)).1.contDiffWithinAt,
    fun v hv => (hsmooth v (hes v hv)).2.contDiffWithinAt, ?_, ?_, ?_⟩
  · intro z hz
    have hv := hes (e.symm z) (e.map_target hz)
    obtain ⟨M, hM⟩ := hd (e.symm z) hv
    exact (e.contDiffAt_symm hz hM (hsmooth (e.symm z) hv).2).contDiffWithinAt
  · intro v hv
    exact ⟨(hU (hes v hv)).2.2.1.1, hlocal v (hes v hv)⟩
  · have hpair : Tendsto (fun p : SectionCoordinates × ℝ => (C p.1, p.2))
        (𝓝 (y, t)) (𝓝 (C y, t)) :=
      (hCy.continuousAt.comp continuousAt_fst).prodMk continuousAt_snd
    exact (continuousAt_fst.eventually (e.open_source.mem_nhds hye)).and (hpair.eventually huniq)

end BianchiIX
