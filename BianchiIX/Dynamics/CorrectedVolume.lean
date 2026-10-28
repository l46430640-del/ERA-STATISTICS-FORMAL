import BianchiIX.Dynamics.FlowDeterminant

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped Topology

/-- Reciprocal of the corrected ambient volume density in the original five coordinates. -/
def normalizedVolumeWeight (x : NormalizedState) : ℝ :=
  x 2 * x 3 * x 4 * (1 + 4 * wallAmplitude (x 2) (x 3) (x 4))

def normalizedCorrectedDivergence (x : NormalizedState) : ℝ :=
  correctedDivergence (curvature (x 2) (x 3) (x 4)) (wallAmplitude (x 2) (x 3) (x 4))

theorem normalizedVolumeWeight_pos {x : NormalizedState} (hx : positiveWalls x) :
    0 < normalizedVolumeWeight x := by
  have hh : 0 ≤ wallAmplitude (x 2) (x 3) (x 4) :=
    Real.rpow_nonneg (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2).le _
  exact mul_pos (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2) (by linarith)

theorem normalizedCorrectedDivergence_pos {x : NormalizedState} (hx : positiveWalls x) :
    0 < normalizedCorrectedDivergence x :=
  corrected_divergence_amplitude_pos hx.1 hx.2.1 hx.2.2

theorem continuousAt_normalizedCorrectedDivergence {x : NormalizedState}
    (hx : positiveWalls x) : ContinuousAt normalizedCorrectedDivergence x := by
  have hh : 0 ≤ wallAmplitude (x 2) (x 3) (x 4) :=
    Real.rpow_nonneg (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2).le _
  have hc : Continuous (fun z : NormalizedState => wallAmplitude (z 2) (z 3) (z 4)) := by
    unfold wallAmplitude
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2 / 3)).comp (by fun_prop)
  unfold normalizedCorrectedDivergence correctedDivergence
  exact (continuousAt_const.mul ((show ContinuousAt
    (fun z : NormalizedState => curvature (z 2) (z 3) (z 4)) x by
      unfold curvature; fun_prop).add (continuousAt_const.mul hc.continuousAt))).div
    (continuousAt_const.add (continuousAt_const.mul hc.continuousAt)) (by linarith)

theorem hasDerivAt_normalizedVolumeWeight {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t)
    (hpos : positiveWalls (α t)) (hcon : stateConstraint (α t) = 1) :
    HasDerivAt (fun u => normalizedVolumeWeight (α u))
      ((normalizedDivergence (α t) - normalizedCorrectedDivergence (α t)) *
        normalizedVolumeWeight (α t)) t := by
  obtain ⟨_, _, ha, hb, hc⟩ := hasDerivAt_normalized_components hα
  have hH := hasDerivAt_wallAmplitude (p := fun u => α u 0) (s := fun u => α u 1)
    ha hb hc hpos.1 hpos.2.1 hpos.2.2
  have hprod := hasDerivAt_wall_product (p := fun u => α u 0) (s := fun u => α u 1) ha hb hc
  have hh : 0 ≤ wallAmplitude (α t 2) (α t 3) (α t 4) :=
    Real.rpow_nonneg (mul_pos (mul_pos hpos.1 hpos.2.1) hpos.2.2).le _
  have heq := corrected_divergence_identity
    (q := curvature (α t 2) (α t 3) (α t 4))
    (s2 := shearSq (α t 0) (α t 1)) hcon hh
  have hne : 1 + 4 * wallAmplitude (α t 2) (α t 3) (α t 4) ≠ 0 := by linarith
  apply (hprod.mul ((hH.const_mul 4).const_add 1)).congr_deriv
  unfold normalizedDivergence normalizedCorrectedDivergence normalizedVolumeWeight
  rw [← heq]
  field_simp [hne]
  ring

/-- Weighted five-dimensional fixed-time Jacobian; restriction to section flux is a further step. -/
def normalizedVolumeJacobian (x : NormalizedState) (t₀ t : ℝ) : ℝ :=
  normalizedVolumeWeight x * (normalizedFlowDifferential x t₀ t).det /
    normalizedVolumeWeight (normalizedMaxCurve x t₀ t)

theorem normalizedVolumeJacobian_initial {x : NormalizedState} (hpos : positiveWalls x) (t₀ : ℝ) :
    normalizedVolumeJacobian x t₀ t₀ = 1 := by
  simp [normalizedVolumeJacobian, normalizedFlowDifferential_initial, ContinuousLinearMap.det,
    normalizedMaxCurve_initial, ne_of_gt (normalizedVolumeWeight_pos hpos)]

theorem hasDerivAt_normalizedVolumeJacobian {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (normalizedVolumeJacobian x t₀)
      (normalizedCorrectedDivergence (normalizedMaxCurve x t₀ t) *
        normalizedVolumeJacobian x t₀ t) t := by
  have hp := (maximalNormalizedSolution x t₀).physical hpos hcon ht
  have hW := hasDerivAt_normalizedVolumeWeight (hasDerivAt_normalizedMaxCurve ht) hp.1 hp.2
  have hne := ne_of_gt (normalizedVolumeWeight_pos hp.1)
  apply (((hasDerivAt_normalizedFlowDeterminant ht).const_mul
    (normalizedVolumeWeight x)).div hW hne).congr_deriv
  unfold normalizedVolumeJacobian
  field_simp [hne]
  ring

theorem normalizedVolumeJacobian_eq_exp_integral {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedVolumeJacobian x t₀ t =
      Real.exp (∫ u in t₀..t, normalizedCorrectedDivergence (normalizedMaxCurve x t₀ u)) := by
  have hc : ContinuousOn (fun u => normalizedCorrectedDivergence (normalizedMaxCurve x t₀ u))
      (normalizedMaxDomain x t₀) := by
    intro u hu
    exact ((continuousAt_normalizedCorrectedDivergence
      ((maximalNormalizedSolution x t₀).physical hpos hcon hu).1).comp
        (hasDerivAt_normalizedMaxCurve hu).continuousAt).continuousWithinAt
  have H := homogeneous_solution_eq_exp_integral (convex_normalizedMaxDomain x t₀)
    (isOpen_normalizedMaxDomain x t₀) hc
    (fun _ hu => hasDerivAt_normalizedVolumeJacobian hpos hcon hu)
    (initial_mem_normalizedMaxDomain x t₀) ht
  simpa only [normalizedVolumeJacobian_initial hpos, one_mul] using H

theorem normalizedVolumeJacobian_gt_one {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1) (htt : t₀ < t) :
    1 < normalizedVolumeJacobian x t₀ t := by
  have hdom := normalizedMaxDomain_contains_Ici hpos hcon t₀
  rw [normalizedVolumeJacobian_eq_exp_integral hpos hcon (hdom htt.le), Real.one_lt_exp_iff]
  have hc : ContinuousOn (fun u => normalizedCorrectedDivergence (normalizedMaxCurve x t₀ u))
      (Icc t₀ t) := by
    intro u hu
    exact ((continuousAt_normalizedCorrectedDivergence
      ((maximalNormalizedSolution x t₀).physical hpos hcon (hdom hu.1)).1).comp
        (hasDerivAt_normalizedMaxCurve (hdom hu.1)).continuousAt).continuousWithinAt
  apply intervalIntegral.integral_pos htt hc
  · intro u hu
    exact (normalizedCorrectedDivergence_pos
      ((maximalNormalizedSolution x t₀).physical hpos hcon (hdom hu.1.le)).1).le
  · exact ⟨t₀, ⟨le_rfl, htt.le⟩, by
      simpa only [normalizedMaxCurve_initial] using normalizedCorrectedDivergence_pos hpos⟩

end BianchiIX
