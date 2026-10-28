import BianchiIX.Measure.BoundedDensity
import BianchiIX.Statistics.EraBudget

/-! The survivor coding density and its exact mass, also on every initial restriction. -/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace BianchiIX.InverseBranchTree

noncomputable section

def codeMeasureOn (T : InverseBranchTree) (I : Set ℝ) : Measure ℝ :=
  Measure.map T.code ((volume.comap (Subtype.val : T.survivors → ℝ)).restrict
    ((Subtype.val : T.survivors → ℝ) ⁻¹' I))

theorem codeMeasureOn_univ (T : InverseBranchTree) :
    T.codeMeasureOn univ = Measure.map T.code (volume.comap (Subtype.val : T.survivors → ℝ)) := by
  simp only [codeMeasureOn, preimage_univ, Measure.restrict_univ]

theorem codeMeasureOn_mass (T : InverseBranchTree) (I : Set ℝ) :
    T.codeMeasureOn I univ = volume (I ∩ T.survivors) := by
  rw [codeMeasureOn, Measure.map_apply T.code_measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, comap_subtype_coe_apply T.survivors_measurable]
  congr 1
  ext x
  simp [and_comm]

namespace BranchEstimates

variable {T : InverseBranchTree} {d e : ℕ → ℝ} (E : T.BranchEstimates d e)

include E

theorem codeMeasureOn_le {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (I : Set ℝ) : T.codeMeasureOn I ≤ Real.toNNReal (Real.exp L) • volume :=
  (Measure.map_mono Measure.restrict_le_self T.code_measurable).trans (E.code_map_le hbudget)

/-- The density is not normalized: all initial stopping losses remain in its mass. -/
theorem codeMeasureOn_density {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (I : Set ℝ) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ᵐ x ∂volume, ρ x ≤ Real.exp L) ∧ Integrable ρ volume ∧
      volume.withDensity (fun x => ENNReal.ofReal (ρ x)) = T.codeMeasureOn I ∧
      (∫ x, ρ x) = (volume (I ∩ T.survivors)).toReal := by
  have hsub : I ∩ T.survivors ⊆ Ioo (0 : ℝ) 1 :=
    inter_subset_right.trans (T.survivors_subset_root.trans E.root_subset)
  have : IsFiniteMeasure (T.codeMeasureOn I) := ⟨by
    rw [T.codeMeasureOn_mass]
    exact (measure_mono hsub).trans_lt (by simp)⟩
  obtain ⟨ρ, hm, hn, hb, hi, heq, hmass⟩ :=
    exists_bounded_density_of_le_smul (E.codeMeasureOn_le hbudget I)
  refine ⟨ρ, hm, hn, ?_, hi, heq, ?_⟩
  · simpa only [Real.coe_toNNReal _ (Real.exp_pos L).le] using hb
  · simpa only [T.codeMeasureOn_mass] using hmass

theorem code_density {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ᵐ x ∂volume, ρ x ≤ Real.exp L) ∧ Integrable ρ volume ∧
      volume.withDensity (fun x => ENNReal.ofReal (ρ x)) =
        Measure.map T.code (volume.comap (Subtype.val : T.survivors → ℝ)) ∧
      (∫ x, ρ x) = (volume T.survivors).toReal := by
  simpa only [T.codeMeasureOn_univ, univ_inter] using E.codeMeasureOn_density hbudget univ

theorem weighted_restricted_root_loss_le {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (ell : ℕ → ℝ≥0∞) (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ell w.length)
    {I : Set ℝ} (hI : MeasurableSet I) {ω : ℝ → ℝ≥0∞} {D : ℝ≥0}
    (hω : ∀ x ∈ T.root, ω x ≤ D) :
    (volume.withDensity ω) ((I ∩ T.root) \ (I ∩ T.survivors)) ≤
      min ((volume.withDensity ω) I)
        ((D : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m)) := by
  have hA := (hI.inter T.root_open.measurableSet).diff (hI.inter T.survivors_measurable)
  refine le_min (measure_mono (sdiff_subset.trans inter_subset_left)) ?_
  rw [withDensity_apply _ hA]
  calc
    _ ≤ ∫⁻ _ in (I ∩ T.root) \ (I ∩ T.survivors), (D : ℝ≥0∞) :=
      setLIntegral_mono' hA (fun x hx => hω x hx.1.2)
    _ = (D : ℝ≥0∞) * volume ((I ∩ T.root) \ (I ∩ T.survivors)) := by simp
    _ ≤ _ := mul_le_mul' le_rfl
      ((E.restricted_root_loss_le I ell hbudget hsize).trans (min_le_right _ _))

end BranchEstimates
end
end BianchiIX.InverseBranchTree
