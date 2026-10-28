import BianchiIX.Statistics.GaussInvariant

/-! Every irrational phase is coded, and Gauss cylinders determine measure domination. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace BianchiIX

theorem gaussMap_iterate_mem_irrational_unit {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hi : Irrational x) (n : ℕ) :
    gaussMap^[n] x ∈ Ioo (0 : ℝ) 1 ∧ Irrational (gaussMap^[n] x) := by
  induction n with
  | zero => exact ⟨hx, hi⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨gaussMap_mem_unit ih.2, gaussMap_irrational ih.2⟩

theorem exists_gaussCode_of_irrational {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hi : Irrational x) :
    ∃ a : ℕ → ℕ+, gaussCode a = x := by
  have hy (n : ℕ) := (gaussMap_iterate_mem_irrational_unit hx hi n).1
  choose j hj using fun n => exists_gauss_inverse (hy n)
  let a : ℕ → ℕ+ := fun n => ⟨j n + 1, Nat.succ_pos _⟩
  have herr (n : ℕ) : inverseError (fun k => (a k : ℕ)) (fun k => gaussMap^[k] x) n = 0 := by
    change |gaussMap^[n] x - gaussInv ((j n + 1 : ℕ) : ℝ) (gaussMap^[n + 1] x)| = 0
    rw [Nat.cast_add, Nat.cast_one, Function.iterate_succ_apply', hj n, sub_self, abs_zero]
  have h := gaussCode_error_bound a (fun n => ⟨(hy n).1.le, (hy n).2.le⟩) 0
  simp only [herr, zero_add, add_zero, mul_zero, tsum_zero, shiftDigits_zero,
    Function.iterate_zero, id_eq] at h
  exact ⟨a, (sub_eq_zero.mp (abs_nonpos_iff.mp h)).symm⟩

theorem exists_digitPrefix (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) :
    ∃ a : ℕ → ℕ+, digitPrefix a w.length = w := by
  let a : ℕ → ℕ+ := fun n => if h : n < w.length then
    ⟨w[n], hw _ (List.getElem_mem h)⟩ else 1
  refine ⟨a, ?_⟩
  apply List.ext_getElem
  · exact digitPrefix_length a w.length
  · intro i hi _
    simp only [digitPrefix, List.length_map, List.length_range] at hi
    simp [digitPrefix, a, hi]

theorem gaussMap_gaussInv_nat {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    {a : ℕ} (ha : 1 ≤ a) : gaussMap (gaussInv a x) = x := by
  have h := gaussMap_inverse hx (a - 1)
  have hc : ((a - 1 : ℕ) : ℝ) + 1 = a := by
    rw [Nat.cast_sub ha, Nat.cast_one, sub_add_cancel]
  rwa [hc] at h

theorem gaussWord_mem_invariant {E : Set ℝ} (hE : gaussMap ⁻¹' E = E)
    (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    gaussWord w x ∈ E ↔ x ∈ E := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hw' : ∀ b ∈ w, 1 ≤ b := fun b hb => hw b (by simp [hb])
    have hmem : gaussMap (gaussInv a (gaussWord w x)) ∈ E ↔
        gaussInv a (gaussWord w x) ∈ E := by
      change gaussInv a (gaussWord w x) ∈ gaussMap ⁻¹' E ↔ _
      rw [hE]
    rw [gaussMap_gaussInv_nat (gaussWord_mem_open_unit w hw' hx) (hw a (by simp))] at hmem
    exact hmem.symm.trans (ih hw')

theorem gaussWord_image_inter_invariant {E : Set ℝ} (hE : gaussMap ⁻¹' E = E)
    (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a) :
    gaussWord w '' (Ioo (0 : ℝ) 1 ∩ E) = gaussCylinder w ∩ E := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxE⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (gaussWord_mem_invariant hE w hw hx).mpr hxE⟩
  · rintro ⟨⟨x, hx, rfl⟩, hyE⟩
    exact ⟨x, ⟨hx, (gaussWord_mem_invariant hE w hw hx).mp hyE⟩, rfl⟩

theorem measure_le_of_gaussCylinder_bounds (μ ν : Measure ℝ) [ν.OuterRegular]
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x)
    (hbound : ∀ w : List ℕ, w ≠ [] → (∀ k ∈ w, 1 ≤ k) →
      μ (gaussCylinder w) ≤ ν (gaussCylinder w)) : μ ≤ ν := by
  have hopen {O : Set ℝ} (hO : IsOpen O) : μ O ≤ ν O := by
    have hcover : μ O ≤ μ (⋃ w ∈ firstGaussCylinders O, gaussCylinder w) := by
      apply measure_mono_ae
      filter_upwards [hμ] with x hx
      intro hxO
      obtain ⟨a, rfl⟩ := exists_gaussCode_of_irrational hx.1 hx.2
      obtain ⟨w, hw, hxw⟩ := gaussCode_mem_first_cylinder hO a hxO
      exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨hw, hxw⟩⟩
    calc
      μ O ≤ μ (⋃ w ∈ firstGaussCylinders O, gaussCylinder w) := hcover
      _ ≤ ∑' w : firstGaussCylinders O, μ (gaussCylinder w.val) :=
        measure_biUnion_le μ (Set.to_countable _) _
      _ ≤ ∑' w : firstGaussCylinders O, ν (gaussCylinder w.val) :=
        ENNReal.tsum_le_tsum (fun w => hbound w.val w.property.2.2.1 w.property.1)
      _ = ν (⋃ w ∈ firstGaussCylinders O, gaussCylinder w) :=
        (measure_biUnion (Set.to_countable _) (firstGaussCylinders_disjoint O)
          (fun w _ => measurableSet_gaussCylinder w)).symm
      _ ≤ ν O := measure_mono (iUnion₂_subset fun _ hw => hw.2.1)
  apply Measure.le_iff.mpr
  intro A _
  rw [A.measure_eq_iInf_isOpen ν]
  exact le_iInf fun O => le_iInf fun hAO => le_iInf fun hO => (measure_mono hAO).trans (hopen hO)

end BianchiIX
