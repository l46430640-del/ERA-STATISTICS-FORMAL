import BianchiIX.Dynamics.SingleStrongReduction
import BianchiIX.Analysis.ClockDecayIntegrals

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def singleStrongDecayRate (m u : ℝ) : ℝ :=
  6 * m * (m - singleStrongLowerRoot (singleStrongInvariant m u)) /
    (2 + singleStrongInvariant m u * singleStrongUpperRoot (singleStrongInvariant m u))

theorem singleStrongDecayRate_pos {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    0 < singleStrongDecayRate m u := by
  have hI := singleStrongInvariant_gt_two hm (Or.inr hu.ne')
  have hq := (singleStrongRoot_relations hI).1
  have ha := (singleStrongRoot_bracket hm hu.ne').1
  unfold singleStrongDecayRate
  positivity

theorem singleStrongFlow_damping_lower {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    singleStrongDecayRate m u ≤
      6 * stableOriginalFlow ![m, u, 0] t 0 *
        (stableOriginalFlow ![m, u, 0] t 0 - singleStrongLowerRoot (singleStrongInvariant m u)) /
        (2 + singleStrongInvariant m u * stableOriginalFlow ![m, u, 0] t 0) := by
  have hI : 0 < singleStrongInvariant m u :=
    lt_trans (by norm_num) (singleStrongInvariant_gt_two hm (Or.inr hu.ne'))
  have ha := (singleStrongRoot_bracket hm hu.ne').1
  have hM := singleStrongFlow_mass_ge hm hu ht
  have hb := (singleStrongFlow_bracket hm hu ht).2
  have hD : 0 < 2 + singleStrongInvariant m u * stableOriginalFlow ![m, u, 0] t 0 := by
    rw [← singleStrongFlow_denom hm hu ht]
    exact stableBoundaryDenom_pos _
  have hN : 0 ≤ 6 * m * (m - singleStrongLowerRoot (singleStrongInvariant m u)) := by positivity
  have hDD : 2 + singleStrongInvariant m u * stableOriginalFlow ![m, u, 0] t 0 ≤
      2 + singleStrongInvariant m u * singleStrongUpperRoot (singleStrongInvariant m u) := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hb.le hI.le)
  have hNN : 6 * m * (m - singleStrongLowerRoot (singleStrongInvariant m u)) ≤
      6 * stableOriginalFlow ![m, u, 0] t 0 *
        (stableOriginalFlow ![m, u, 0] t 0 - singleStrongLowerRoot (singleStrongInvariant m u)) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num))
      (sub_le_sub_right hM _) (sub_nonneg.mpr ha.le)
      (mul_nonneg (by norm_num) (hm.le.trans hM))
  exact (div_le_div_of_nonneg_left hN hD hDD).trans
    (div_le_div_of_nonneg_right hNN hD.le)

theorem singleStrongFlow_gap_exp {m u t : ℝ} (hm : 0 < m) (hu : 0 < u) (ht : 0 ≤ t) :
    |singleStrongUpperRoot (singleStrongInvariant m u) - stableOriginalFlow ![m, u, 0] t 0| ≤
      (singleStrongUpperRoot (singleStrongInvariant m u) - m) * Real.exp (-singleStrongDecayRate m u * t) := by
  let I := singleStrongInvariant m u
  let a := singleStrongLowerRoot I
  let b := singleStrongUpperRoot I
  let M := fun s => stableOriginalFlow ![m, u, 0] s 0
  let d := fun s => -(6 * M s * (M s - a) / (2 + I * M s))
  have hf (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt (fun r => b - M r) (1 * (d s * (b - M s))) s := by
    convert! (hasDerivAt_singleStrongFlow_reduced hm hu hs.1).const_sub b using 1
    ring
  have hd (s : ℝ) (hs : s ∈ Icc 0 t) : d s ≤ -singleStrongDecayRate m u :=
    neg_le_neg (singleStrongFlow_damping_lower hm hu hs.1)
  have H := abs_le_exp_of_clock_damping (z := fun s => s) (z' := fun _ => 1)
    hf (fun s _ => hasDerivAt_id s) (fun _ _ => by norm_num) hd t ⟨ht, le_rfl⟩
  have hb := (singleStrongRoot_bracket hm hu.ne').2
  simpa [M, b, I, stableOriginalFlow_initial, abs_of_pos (sub_pos.mpr hb)] using H

theorem singleStrongFlow_mass_limit {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    Tendsto (fun t => stableOriginalFlow ![m, u, 0] t 0) atTop
      (𝓝 (singleStrongUpperRoot (singleStrongInvariant m u))) := by
  have hexp : Tendsto (fun t => Real.exp (-singleStrongDecayRate m u * t)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (singleStrongDecayRate_pos hm hu) (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)) using 1
    ext t
    congr 1
    simp only [id_eq, neg_mul]
  have habs : Tendsto (fun t => |singleStrongUpperRoot (singleStrongInvariant m u) -
      stableOriginalFlow ![m, u, 0] t 0|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_
      (by simpa only [mul_zero] using hexp.const_mul (singleStrongUpperRoot (singleStrongInvariant m u) - m))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact singleStrongFlow_gap_exp hm hu ht
  have hgap : Tendsto (fun t => singleStrongUpperRoot (singleStrongInvariant m u) -
      stableOriginalFlow ![m, u, 0] t 0) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr habs
  simpa only [sub_zero, sub_sub_cancel] using
    (tendsto_const_nhds (x := singleStrongUpperRoot (singleStrongInvariant m u))).sub hgap

theorem singleStrongFlow_wall_limit {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    Tendsto (fun t => stableOriginalFlow ![m, u, 0] t 1) atTop (𝓝 0) := by
  have hM := singleStrongFlow_mass_limit hm hu
  have hsq : Tendsto (fun t => stableOriginalFlow ![m, u, 0] t 1 ^ 2) atTop (𝓝 0) := by
    have H := (hM.sub_const (singleStrongLowerRoot (singleStrongInvariant m u))).mul
      ((tendsto_const_nhds (x := singleStrongUpperRoot (singleStrongInvariant m u))).sub hM)
    apply (tendsto_congr' ?_).mpr (by simpa only [sub_self, mul_zero] using H)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact singleStrongFlow_factorization hm hu ht
  have habs : Tendsto (fun t => |stableOriginalFlow ![m, u, 0] t 1|) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using hsq.sqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr habs

theorem singleStrongFlow_limit {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    Tendsto (stableOriginalFlow ![m, u, 0]) atTop
      (𝓝 ![singleStrongUpperRoot (singleStrongInvariant m u), 0, 0]) := by
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact singleStrongFlow_mass_limit hm hu
  · exact singleStrongFlow_wall_limit hm hu
  · apply (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (singleStrongFlow_global_region hm hu ht).2.2.1

theorem stableBoundaryProjection_strong_global {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    stableBoundaryProjection m u 0 = singleStrongUpperRoot (singleStrongInvariant m u) := by
  have H : Tendsto (fun t => stableBoundaryOrbit m u 0 t 0) atTop
      (𝓝 (singleStrongUpperRoot (singleStrongInvariant m u))) := by
    simpa [stableOriginalFlow_eq, stableRestriction_apply] using singleStrongFlow_mass_limit hm hu
  exact H.limUnder_eq

theorem singleStrongFlow_normalized_limit {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    Tendsto (normalizedMaxCurve (fromProjectiveState (stableInclusion ![m, u, 0])) 0) atTop
      (𝓝 (fromProjectiveState (stableInclusion ![singleStrongUpperRoot (singleStrongInvariant m u), 0, 0]))) := by
  let z : StableState := ![singleStrongUpperRoot (singleStrongInvariant m u), 0, 0]
  have hD : 0 < projectiveStateDenom (stableInclusion z) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos z
  have H := (contDiffAt_fromProjectiveState 0 hD.ne').continuousAt.tendsto.comp
    ((stableInclusion.continuous.tendsto z).comp (singleStrongFlow_limit hm hu))
  apply (tendsto_congr' ?_).mp H
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change fromProjectiveState (stableInclusion (stableRestriction
    (projectiveOriginalFlow (stableInclusion ![m, u, 0]) 0 t))) = _
  rw [stableInclusion_restriction (stableProjectiveFlow_active_zero _ ht)]
  have hDi : 0 < projectiveStateDenom (stableInclusion ![m, u, 0]) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos _
  have hx := fromProjectiveState_constraint hDi.ne'
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  exact fromProjectiveState_toProjectiveState
    (singleStrongFlow_global_region hm hu ht).2.2.2.ne'
    ((normalizedMaxCurve_constraint hdom).trans hx)

end BianchiIX
