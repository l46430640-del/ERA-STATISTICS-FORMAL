import BianchiIX.Statistics.GaussPartition
import BianchiIX.Statistics.ObservableTransfer
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Cylinder frequencies determine every continuous-observable average on the same typical set. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace BianchiIX

noncomputable section

def gaussRepresentative (n : ℕ) (w : GaussWords n) : ℝ := gaussWord w.val 0

theorem gaussRepresentative_mem_unit (n : ℕ) (w : GaussWords n) :
    gaussRepresentative n w ∈ Icc (0 : ℝ) 1 :=
  gaussWord_mem_unit _ w.property.2 ⟨le_rfl, zero_le_one⟩

theorem gaussCylinder_distance_representative (n : ℕ) (w : GaussWords n)
    {x : ℝ} (hx : x ∈ gaussCylinder w.val) :
    |x - gaussRepresentative n w| ≤ (1 / 4 : ℝ) ^ (n / 2) := by
  obtain ⟨t, ht, rfl⟩ := hx
  simpa only [gaussRepresentative, w.property.1] using
    gaussWord_diameter w.val w.property.2 ⟨ht.1.le, ht.2.le⟩ ⟨le_rfl, zero_le_one⟩

theorem integrable_gauss_continuous {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Integrable f gaussMeasure := by
  have hmem : ∀ᵐ x ∂gaussMeasure, x ∈ Icc (0 : ℝ) 1 :=
    ae_gaussMeasure_mem_unit.mono (fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  have h := hf.integrableOn_Icc (μ := gaussMeasure)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hmem] at h

theorem hasSum_gaussCylinder_integral {f : ℝ → ℝ} (hf : Integrable f gaussMeasure) (n : ℕ) :
    HasSum (fun w : GaussWords n => ∫ x in gaussCylinder w.val, f x ∂gaussMeasure)
      (∫ x, f x ∂gaussMeasure) := by
  have h := hasSum_integral_iUnion (fun w : GaussWords n => measurableSet_gaussCylinder w.val)
    (gaussWords_disjoint n) hf.integrableOn
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_gaussWords_cover n)] at h

theorem gaussRepresentative_integral_error {f : ℝ → ℝ} (hf : Integrable f gaussMeasure)
    (n : ℕ) {M ε : ℝ} (hb : ∀ w, |f (gaussRepresentative n w)| ≤ M)
    (hosc : ∀ (w : GaussWords n) x, x ∈ gaussCylinder w.val →
      |f x - f (gaussRepresentative n w)| ≤ ε) :
    |(∫ x, f x ∂gaussMeasure) - ∑' w, gaussMass n w * f (gaussRepresentative n w)| ≤ ε := by
  have hi := hasSum_gaussCylinder_integral hf n
  have hr := summable_probability_weighted (gaussMass_nonneg n) (gaussMass_hasSum n) hb
  have hd := (hi.summable.sub hr).abs
  have hcell (w : GaussWords n) :
      |(∫ x in gaussCylinder w.val, f x ∂gaussMeasure) -
        gaussMass n w * f (gaussRepresentative n w)| ≤ ε * gaussMass n w := by
    have hbound := norm_setIntegral_le_of_norm_le_const_ae
      (measure_lt_top gaussMeasure (gaussCylinder w.val))
      ((ae_restrict_mem (measurableSet_gaussCylinder w.val)).mono
        (fun x hx => (show ‖f x - f (gaussRepresentative n w)‖ ≤ ε from
          (Real.norm_eq_abs _).trans_le (hosc w x hx))))
    rw [integral_sub hf.integrableOn (integrable_const _), setIntegral_const] at hbound
    simpa only [Real.norm_eq_abs, smul_eq_mul, Measure.real, gaussMass] using hbound
  rw [← hi.tsum_eq, ← hi.summable.tsum_sub hr]
  calc
    _ ≤ ∑' w : GaussWords n, |(∫ x in gaussCylinder w.val, f x ∂gaussMeasure) -
        gaussMass n w * f (gaussRepresentative n w)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
        (f := fun w : GaussWords n => (∫ x in gaussCylinder w.val, f x ∂gaussMeasure) -
          gaussMass n w * f (gaussRepresentative n w))
        (by simpa only [Real.norm_eq_abs] using hd)
    _ ≤ ∑' w, ε * gaussMass n w := hd.tsum_le_tsum hcell ((gaussMass_hasSum n).summable.mul_left ε)
    _ = ε := by rw [tsum_mul_left, (gaussMass_hasSum n).tsum_eq, mul_one]

theorem gaussRepresentative_uniform_approximation {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∀ (w : GaussWords n) x, x ∈ gaussCylinder w.val →
      |f x - f (gaussRepresentative n w)| ≤ ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  obtain ⟨n, hn⟩ := ((tendsto_order.mp gauss_diameter_tendsto_zero).2 δ hδ).exists
  refine ⟨n, fun w x hx => ?_⟩
  have hxunit : x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨t, ht, rfl⟩ := hx
    exact gaussWord_mem_unit w.val w.property.2 ⟨ht.1.le, ht.2.le⟩
  have hdist : dist x (gaussRepresentative n w) < δ := by
    rw [Real.dist_eq]
    exact (gaussCylinder_distance_representative n w hx).trans_lt hn
  simpa only [Real.dist_eq] using
    (hclose x hxunit (gaussRepresentative n w) (gaussRepresentative_mem_unit n w) hdist).le

private theorem timeAverage_abs_le {u : ℕ → ℝ} {ε : ℝ} (hu : ∀ j, |u j| ≤ ε)
    (N : ℕ) : |timeAverage u (N + 1)| ≤ ε := by
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  rw [timeAverage, abs_mul, abs_of_pos (inv_pos.mpr hN)]
  calc
    _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ j ∈ Finset.range (N + 1), |u j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hN.le)
    _ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ * ∑ _j ∈ Finset.range (N + 1), ε :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hu j)) (inv_nonneg.mpr hN.le)
    _ = ε := by simp [show (N : ℝ) + 1 ≠ 0 by positivity]

theorem gaussRepresentative_average_error (a : ℕ → ℕ+) {f : ℝ → ℝ} (n N : ℕ) {ε : ℝ}
    (hosc : ∀ (w : GaussWords n) x, x ∈ gaussCylinder w.val →
      |f x - f (gaussRepresentative n w)| ≤ ε) :
    |timeAverage (fun j => f (gaussMap^[j] (gaussCode a))) (N + 1) -
      ∑' w, gaussEmpiricalMass a n N w * f (gaussRepresentative n w)| ≤ ε := by
  simp only [gaussEmpiricalMass]
  rw [(empiricalMass_weighted_hasSum
    (fun j => gaussPrefixWord (shiftDigits a j) n) N (fun w => f (gaussRepresentative n w))).tsum_eq]
  change |timeAverage _ (N + 1) - timeAverage _ (N + 1)| ≤ ε
  rw [← timeAverage_sub]
  apply timeAverage_abs_le
  intro j
  rw [gaussMap_iterate_code]
  exact hosc (gaussPrefixWord (shiftDigits a j) n) _ (gaussCode_mem_cylinder (shiftDigits a j) n)

theorem gauss_continuous_average (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Tendsto (timeAverage (fun j => f (gaussMap^[j] (gaussCode a)))) atTop
      (𝓝 (∫ x, f x ∂gaussMeasure)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := gaussRepresentative_uniform_approximation hf (show 0 < ε / 3 by linarith)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hb (w : GaussWords n) : |f (gaussRepresentative n w)| ≤ M := by
    simpa only [Real.norm_eq_abs] using hM _ (gaussRepresentative_mem_unit n w)
  have hi := gaussRepresentative_integral_error (integrable_gauss_continuous hf) n hb hn
  have hp := gaussEmpiricalMass_weighted_tendsto a ha n hb
  filter_upwards [Metric.tendsto_nhds.mp hp (ε / 3) (by linarith)] with N hN
  rw [Real.dist_eq] at hN ⊢
  have he := gaussRepresentative_average_error a n N hn
  have htri := abs_sub_le
    (timeAverage (fun j => f (gaussMap^[j] (gaussCode a))) (N + 1))
    (∑' w, gaussEmpiricalMass a n N w * f (gaussRepresentative n w))
    (∫ x, f x ∂gaussMeasure)
  have htri' := abs_sub_le
    (∑' w, gaussEmpiricalMass a n N w * f (gaussRepresentative n w))
    (∑' w, gaussMass n w * f (gaussRepresentative n w)) (∫ x, f x ∂gaussMeasure)
  rw [abs_sub_comm (∑' w, gaussMass n w * f (gaussRepresentative n w))] at htri'
  linarith

namespace InverseBranchTree.BranchEstimates

theorem ae_continuous_timeAverage {T : InverseBranchTree} {d e : ℕ → ℝ}
    (E : T.BranchEstimates d e) (hB : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (hd : Tendsto d atTop (𝓝 0)) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), ∀ f : ℝ → ℝ,
      ContinuousOn f (Icc (0 : ℝ) 1) →
      Tendsto (timeAverage (fun n => f (T.phase x n))) atTop (𝓝 (∫ y, f y ∂gaussMeasure)) := by
  filter_upwards [E.ae_code_gaussCylinderTypical hB hbudget] with x hx
  intro f hf
  exact E.continuous_timeAverage hd x hf (gauss_continuous_average (T.digits x) hx hf)

end InverseBranchTree.BranchEstimates
end
end BianchiIX
