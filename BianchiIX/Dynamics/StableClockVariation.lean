import BianchiIX.Dynamics.StableClockFlow
import BianchiIX.Analysis.ParameterSlice
import BianchiIX.Analysis.ParametricVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableClockVariationRate (c : ℝ) (w : StableState) (p : StableState × ℝ) : StableState :=
  fderiv ℝ (stableClockField c) (stableClockFlow c p) (fderiv ℝ (stableClockFlow c) p (w, 0))

theorem contDiffAt_stableClockVariationRate_one {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (w : StableState) :
    ContDiffAt ℝ 1 (stableClockVariationRate c w) (y, σ) := by
  have hΦ := contDiffAt_stableClockFlow_two hc hy hσ
  have hA := ((contDiff_stableClockField c 2).contDiffAt.fderiv_right
    (m := 1) (by norm_num)).comp (y, σ) (hΦ.of_le (by norm_num))
  exact hA.clm_apply (contDiffAt_parameterVariation hΦ w)

theorem stableClockFlow_local_partial_time {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 < σ) :
    (fun p => fderiv ℝ (stableClockFlow c) p (0, 1)) =ᶠ[𝓝 (y, σ)]
      (fun p => stableClockField c (stableClockFlow c p)) := by
  filter_upwards [((isOpen_stableParameterDomain c).prod isOpen_Ioi).mem_nhds ⟨hy, hσ⟩] with p hp
  have hpath : HasDerivAt (fun s : ℝ => (p.1, s)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have H := ((contDiffAt_stableClockFlow_two hc hp.1 (le_of_lt hp.2)).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (p.1, s)) p.2 hpath
  exact H.unique (hasDerivAt_stableClockFlow_time hc hp.1 (le_of_lt hp.2))

theorem hasDerivAt_stableClockFlow_variation_pos {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 < σ) (v : StableState) :
    HasDerivAt (fun s => fderiv ℝ (stableClockFlow c) (y, s) (v, 0))
      (stableClockVariationRate c v (y, σ)) σ := by
  have hf : DifferentiableAt ℝ (fun p : ℝ × StableState => stableClockField c p.2)
      (σ, stableClockFlow c (y, σ)) :=
    ((contDiff_stableClockField c 1).comp contDiff_snd).differentiable (by norm_num) _
  exact hasDerivAt_parametric_first_variation (contDiffAt_stableClockFlow_two hc hy hσ.le)
    hf (stableClockFlow_local_partial_time hc hy hσ) v

/-- Continuity of the second derivative extends the first variation to the initial time. -/
theorem hasDerivAt_stableClockFlow_variation {c σ : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hσ : 0 ≤ σ) (v : StableState) :
    HasDerivAt (fun s => fderiv ℝ (stableClockFlow c) (y, s) (v, 0))
      (stableClockVariationRate c v (y, σ)) σ := by
  rcases hσ.eq_or_lt with rfl | hσ
  · let J : ℝ → StableState := fun s => fderiv ℝ (stableClockFlow c) (y, s) (v, 0)
    have hJ : ContDiffAt ℝ 1 J 0 :=
      (contDiffAt_parameterVariation (contDiffAt_stableClockFlow_two hc hy le_rfl) v).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)
    have hD : ContinuousAt (deriv J) 0 :=
      (hJ.continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
    have hR : ContinuousAt (fun s => stableClockVariationRate c v (y, s)) 0 :=
      (contDiffAt_stableClockVariationRate_one hc hy le_rfl v).continuousAt.comp
        (continuousAt_const.prodMk continuousAt_id)
    have he : deriv J =ᶠ[𝓝[>] 0] (fun s => stableClockVariationRate c v (y, s)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hasDerivAt_stableClockFlow_variation_pos hc hy hs v).deriv
    have hval : deriv J 0 = stableClockVariationRate c v (y, 0) :=
      tendsto_nhds_unique ((hD.tendsto.mono_left nhdsWithin_le_nhds).congr' he)
        (hR.tendsto.mono_left nhdsWithin_le_nhds)
    simpa only [hval] using (hJ.differentiableAt (by norm_num)).hasDerivAt
  · exact hasDerivAt_stableClockFlow_variation_pos hc hy hσ v

theorem stableClockFlow_variation_initial {c : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (v : StableState) :
    fderiv ℝ (stableClockFlow c) (y, 0) (v, 0) = v := by
  rw [← fderiv_parameterSlice_apply
    ((contDiffAt_stableClockFlow_two hc hy le_rfl).differentiableAt (by norm_num))]
  have he : (fun z => stableClockFlow c (z, 0)) = id := funext (stableClockFlow_initial hc)
  rw [he, fderiv_id]
  rfl

end BianchiIX
