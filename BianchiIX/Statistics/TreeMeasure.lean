import BianchiIX.Statistics.TreeCoding

/-! Distortion and stopping-loss bounds on the recursively constructed branch tree. -/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace BianchiIX

def extendPositiveWord (w : List ℕ+) (n : ℕ) : ℕ+ := w[n]?.getD 1

theorem digitPrefix_extendPositiveWord (w : List ℕ+) :
    digitPrefix (extendPositiveWord w) w.length = w.map (fun a : ℕ+ => (a : ℕ)) := by
  apply List.ext_getElem
  · simp [digitPrefix]
  · intro i hi hj
    simp only [digitPrefix, List.length_map, List.length_range] at hi
    simp [digitPrefix, extendPositiveWord, hi]

namespace InverseBranchTree

variable (T : InverseBranchTree)

theorem terminal_subset {S : Set ℝ} (hroot : T.root ⊆ S)
    (hdom : ∀ w a, T.domain w a ⊆ S) (w : List ℕ+) : T.terminal w ⊆ S := by
  induction w using List.reverseRecOn with
  | nil => simpa using hroot
  | append_singleton w a _ =>
    rw [terminal_append]
    exact inter_subset_left.trans (hdom w a)

theorem cell_volume_le (w : List ℕ+) {L : ℝ}
    (hK : T.terminal w ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ x ∈ T.terminal w, DifferentiableAt ℝ (T.toRoot w) x)
    (hbound : ∀ x ∈ T.terminal w, |deriv (T.toRoot w) x| ≤
      Real.exp L * |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) :
    volume (T.cell w) ≤ ENNReal.ofReal (Real.exp L) *
      volume (gaussCylinder (w.map (fun a : ℕ+ => (a : ℕ)))) := by
  have h := gaussPrefix_cylinder_measure_le (extendPositiveWord w) w.length (L := L)
    (T.terminal_open w).measurableSet hK hF (T.toRoot_injective w)
  simpa only [cell, digitPrefix_extendPositiveWord] using h
    (by simpa only [digitPrefix_extendPositiveWord] using hbound)

theorem code_volume_map_le (L : ℝ)
    (hK : ∀ w, T.terminal w ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ w, ∀ x ∈ T.terminal w, DifferentiableAt ℝ (T.toRoot w) x)
    (hbound : ∀ w, ∀ x ∈ T.terminal w, |deriv (T.toRoot w) x| ≤
      Real.exp L * |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) :
    Measure.map T.code (volume.comap (Subtype.val : T.survivors → ℝ)) ≤
      Real.toNNReal (Real.exp L) • volume := by
  apply T.code_map_le_of_cell_bounds
  intro w _
  exact T.cell_volume_le w (hK w) (hF w) (hbound w)

theorem root_loss_le (ell : ℕ → ℝ≥0∞) (L : ℝ)
    (hK : ∀ w, T.terminal w ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ w, ∀ x ∈ T.terminal w, DifferentiableAt ℝ (T.toRoot w) x)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ell w.length)
    (hbound : ∀ w, ∀ x ∈ T.terminal w, |deriv (T.toRoot w) x| ≤
      Real.exp L * |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) :
    volume (T.root \ T.survivors) ≤ 2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m := by
  rw [survivors, T.root_sdiff_survivors]
  apply stopped_total_mass_le
    (fun m (w : {w : List ℕ+ // w.length = m}) => extendPositiveWord w.val)
    (fun m (w : {w : List ℕ+ // w.length = m}) => T.toRoot w.val)
    (fun m (w : {w : List ℕ+ // w.length = m}) => T.stoppedDomain w.val) ell L
  · intro m v w heq
    apply Subtype.ext
    apply List.map_injective_iff.mpr Subtype.val_injective
    have hv := digitPrefix_extendPositiveWord v.val
    have hw := digitPrefix_extendPositiveWord w.val
    rw [v.property] at hv
    rw [w.property] at hw
    exact hv.symm.trans (heq.trans hw)
  · exact fun _ w => T.stoppedDomain_measurable w.val
  · exact fun _ w => sdiff_subset.trans (hK w.val)
  · exact fun _ w x hx => hF w.val x hx.1
  · exact fun _ w => (T.toRoot_injective w.val).mono sdiff_subset
  · intro m w
    simpa only [w.property] using hsize w.val
  · intro m w x hx
    simpa only [← w.property, digitPrefix_extendPositiveWord] using hbound w.val x hx.1

theorem restricted_root_loss_le (I : Set ℝ) (ell : ℕ → ℝ≥0∞) (L : ℝ)
    (hK : ∀ w, T.terminal w ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ w, ∀ x ∈ T.terminal w, DifferentiableAt ℝ (T.toRoot w) x)
    (hsize : ∀ w, volume (T.stoppedDomain w) ≤ ell w.length)
    (hbound : ∀ w, ∀ x ∈ T.terminal w, |deriv (T.toRoot w) x| ≤
      Real.exp L * |deriv (gaussWord (w.map (fun a : ℕ+ => (a : ℕ)))) x|) :
    volume ((I ∩ T.root) \ (I ∩ T.survivors)) ≤
      min (volume I) (2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m) := by
  have heq : (I ∩ T.root) \ (I ∩ T.survivors) = I ∩ (T.root \ T.survivors) := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [heq]
  exact restricted_stopped_mass_le (T.root_loss_le ell L hK hF hsize hbound)

end InverseBranchTree
end BianchiIX
