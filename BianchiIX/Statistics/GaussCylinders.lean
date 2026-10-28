import BianchiIX.Statistics.GaussCoding
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular

/-! Gauss cylinders and the passage from cylinder bounds to measure domination. -/

namespace BianchiIX

noncomputable section

open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

def gaussCylinder (w : List ℕ) : Set ℝ := gaussWord w '' Ioo 0 1

theorem measurableEmbedding_gaussInv (a : ℝ) : MeasurableEmbedding (gaussInv a) := by
  have h : MeasurableEmbedding (fun x : ℝ => (a + x)⁻¹) :=
    (MeasurableEquiv.inv ℝ).measurableEmbedding.comp
      (MeasurableEquiv.addLeft a).measurableEmbedding
  change MeasurableEmbedding (fun x : ℝ => 1 / (a + x))
  simpa only [one_div] using h

theorem measurableEmbedding_gaussWord (w : List ℕ) : MeasurableEmbedding (gaussWord w) := by
  induction w with
  | nil => exact MeasurableEmbedding.id
  | cons a w ih => exact (measurableEmbedding_gaussInv a).comp ih

theorem measurableSet_gaussCylinder (w : List ℕ) : MeasurableSet (gaussCylinder w) :=
  (measurableEmbedding_gaussWord w).measurableSet_image.mpr measurableSet_Ioo

theorem gaussWord_mem_open_unit (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : gaussWord w x ∈ Ioo (0 : ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    have ht := ih (fun b hb => hw b (by simp [hb]))
    refine ⟨gaussInv_pos ha ht.1.le, ?_⟩
    change 1 / ((a : ℝ) + gaussWord w x) < 1
    exact (div_lt_one (by linarith [ht.1])).mpr (by linarith [ht.1])

theorem gaussCode_mem_cylinder (a : ℕ → ℕ+) (n : ℕ) :
    gaussCode a ∈ gaussCylinder (digitPrefix a n) :=
  ⟨gaussCode (shiftDigits a n),
    ⟨gaussCode_pos _, gaussCode_lt_one _⟩, (gaussCode_prefix a n).symm⟩

theorem gaussCylinder_subset_of_prefix {v w : List ℕ}
    (hw : ∀ a ∈ w, 1 ≤ a) (h : v <+: w) : gaussCylinder w ⊆ gaussCylinder v := by
  rcases h with ⟨t, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨gaussWord t x, gaussWord_mem_open_unit t (fun a ha => hw a (by simp [ha])) hx, ?_⟩
  exact (gaussWord_append v t x).symm

private theorem gaussInv_digit {a : ℕ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ⌊1 / gaussInv a x⌋ = (a : ℤ) := by
  simp only [gaussInv, one_div_one_div]
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> linarith [hx.1, hx.2]

theorem gaussCylinder_comparable {v w : List ℕ}
    (hv : ∀ a ∈ v, 1 ≤ a) (hw : ∀ a ∈ w, 1 ≤ a)
    (h : (gaussCylinder v ∩ gaussCylinder w).Nonempty) : v <+: w ∨ w <+: v := by
  induction v generalizing w with
  | nil => exact Or.inl List.nil_prefix
  | cons a v ih =>
    cases w with
    | nil => exact Or.inr List.nil_prefix
    | cons b w =>
      rcases h with ⟨z, ⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
      have hv' : ∀ c ∈ v, 1 ≤ c := fun c hc => hv c (by simp [hc])
      have hw' : ∀ c ∈ w, 1 ≤ c := fun c hc => hw c (by simp [hc])
      have hval : gaussInv a (gaussWord v x) = gaussInv b (gaussWord w y) :=
        hxz.trans hyz.symm
      have hab : a = b := by
        have hd := congrArg (fun z : ℝ => ⌊1 / z⌋) hval
        rw [gaussInv_digit (gaussWord_mem_open_unit v hv' hx),
          gaussInv_digit (gaussWord_mem_open_unit w hw' hy)] at hd
        exact_mod_cast hd
      subst b
      have htail := (measurableEmbedding_gaussInv a).injective hval
      have hi : (gaussCylinder v ∩ gaussCylinder w).Nonempty :=
        ⟨gaussWord v x, ⟨x, hx, rfl⟩, ⟨y, hy, htail.symm⟩⟩
      simpa only [List.cons_prefix_cons, true_and, eq_self] using ih hv' hw' hi

theorem gaussCode_mem_cylinder_iff (a : ℕ → ℕ+) (w : List ℕ)
    (hw : ∀ k ∈ w, 1 ≤ k) :
    gaussCode a ∈ gaussCylinder w ↔ digitPrefix a w.length = w := by
  constructor
  · intro h
    have hc := gaussCylinder_comparable (digitPrefix_positive a w.length) hw
      ⟨gaussCode a, gaussCode_mem_cylinder a w.length, h⟩
    rcases hc with hc | hc
    · exact hc.eq_of_length (digitPrefix_length a w.length)
    · exact (hc.eq_of_length (digitPrefix_length a w.length).symm).symm
  · intro h
    rw [← h]
    exact gaussCode_mem_cylinder a w.length

theorem exists_gaussCylinder_subset {O : Set ℝ} (hO : IsOpen O)
    (a : ℕ → ℕ+) (ha : gaussCode a ∈ O) :
    ∃ n, gaussCylinder (digitPrefix a (n + 1)) ⊆ O := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (gaussCode a) ha
  have hlim := gauss_diameter_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).2 ε hε).exists
  refine ⟨n, fun x hx => hball ?_⟩
  rcases hx with ⟨t, ht, rfl⟩
  rw [Metric.mem_ball, Real.dist_eq, gaussCode_prefix a (n + 1)]
  exact (gaussWord_diameter _ (digitPrefix_positive a (n + 1))
    ⟨ht.1.le, ht.2.le⟩ (gaussCode_mem_unit _)).trans_lt
      (by simpa only [digitPrefix_length, Function.comp_def] using hn)

def firstGaussCylinders (O : Set ℝ) : Set (List ℕ) :=
  {w | (∀ k ∈ w, 1 ≤ k) ∧ gaussCylinder w ⊆ O ∧ w ≠ [] ∧
    ∀ v, v ≠ [] → v <+: w → v.length < w.length → ¬ gaussCylinder v ⊆ O}

theorem gaussCode_mem_first_cylinder {O : Set ℝ} (hO : IsOpen O)
    (a : ℕ → ℕ+) (ha : gaussCode a ∈ O) :
    ∃ w ∈ firstGaussCylinders O, gaussCode a ∈ gaussCylinder w := by
  classical
  have hex := exists_gaussCylinder_subset hO a ha
  let n := Nat.find hex
  refine ⟨digitPrefix a (n + 1), ⟨digitPrefix_positive a (n + 1), Nat.find_spec hex,
    ?_, ?_⟩, gaussCode_mem_cylinder a (n + 1)⟩
  · intro heq
    have hlen := digitPrefix_length a (n + 1)
    rw [heq] at hlen
    simp at hlen
  intro v hvne hv hvlen hsub
  have hvpos : ∀ k ∈ v, 1 ≤ k :=
    fun k hk => digitPrefix_positive a (n + 1) k (hv.sublist.subset hk)
  have hmem := gaussCylinder_subset_of_prefix (digitPrefix_positive a (n + 1)) hv
    (gaussCode_mem_cylinder a (n + 1))
  have heq := (gaussCode_mem_cylinder_iff a v hvpos).mp hmem
  have hpos : 0 < v.length := List.length_pos_iff.mpr hvne
  have hlt : v.length - 1 < n := by
    simp only [digitPrefix_length] at hvlen
    omega
  apply Nat.find_min hex hlt
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ v.length), heq] using hsub

theorem firstGaussCylinders_disjoint (O : Set ℝ) :
    (firstGaussCylinders O).PairwiseDisjoint gaussCylinder := by
  intro v hv w hw hne
  apply Set.disjoint_left.mpr
  intro x hxv hxw
  rcases gaussCylinder_comparable hv.1 hw.1 ⟨x, hxv, hxw⟩ with hp | hp
  · have hlt : v.length < w.length := lt_of_le_of_ne hp.length_le
      (fun heq => hne (hp.eq_of_length heq))
    exact hw.2.2.2 v hv.2.2.1 hp hlt hv.2.1
  · have hlt : w.length < v.length := lt_of_le_of_ne hp.length_le
      (fun heq => hne (hp.eq_of_length heq).symm)
    exact hv.2.2.2 w hw.2.2.1 hp hlt hw.2.1

theorem gaussCode_preimage_open_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) (a : X → ℕ → ℕ+)
    (hbound : ∀ w : List ℕ, w ≠ [] → (∀ k ∈ w, 1 ≤ k) →
      μ {x | digitPrefix (a x) w.length = w} ≤ ν (gaussCylinder w))
    {O : Set ℝ} (hO : IsOpen O) :
    μ ((gaussCode ∘ a) ⁻¹' O) ≤ ν O := by
  have hcover : (gaussCode ∘ a) ⁻¹' O ⊆
      ⋃ w ∈ firstGaussCylinders O, {x | digitPrefix (a x) w.length = w} := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := gaussCode_mem_first_cylinder hO (a x) hx
    exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨hw,
      (gaussCode_mem_cylinder_iff (a x) w hw.1).mp hxw⟩⟩
  calc
    μ ((gaussCode ∘ a) ⁻¹' O) ≤
        μ (⋃ w ∈ firstGaussCylinders O, {x | digitPrefix (a x) w.length = w}) :=
      measure_mono hcover
    _ ≤ ∑' w : firstGaussCylinders O, μ {x | digitPrefix (a x) w.val.length = w.val} :=
      measure_biUnion_le μ (Set.to_countable _) _
    _ ≤ ∑' w : firstGaussCylinders O, ν (gaussCylinder w.val) :=
      ENNReal.tsum_le_tsum (fun w => hbound w.val w.property.2.2.1 w.property.1)
    _ = ν (⋃ w ∈ firstGaussCylinders O, gaussCylinder w) :=
      (measure_biUnion (Set.to_countable _) (firstGaussCylinders_disjoint O)
        (fun w _ => measurableSet_gaussCylinder w)).symm
    _ ≤ ν O := measure_mono (iUnion₂_subset fun _ hw => hw.2.1)

/-- Prefix mass bounds imply domination for every measurable image set. -/
theorem gaussCode_map_le_of_cylinder_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [ν.OuterRegular] (a : X → ℕ → ℕ+)
    (ha : Measurable a)
    (hbound : ∀ w : List ℕ, w ≠ [] → (∀ k ∈ w, 1 ≤ k) →
      μ {x | digitPrefix (a x) w.length = w} ≤ ν (gaussCylinder w)) :
    Measure.map (gaussCode ∘ a) μ ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply (measurable_gaussCode.comp ha) hs, s.measure_eq_iInf_isOpen ν]
  apply le_iInf
  intro O
  apply le_iInf
  intro hsO
  apply le_iInf
  intro hO
  exact (measure_mono (preimage_mono hsO)).trans (gaussCode_preimage_open_le μ ν a hbound hO)

theorem gaussCode_map_le_smul_of_cylinder_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [ν.OuterRegular] (a : X → ℕ → ℕ+)
    (ha : Measurable a) (C : ℝ≥0)
    (hbound : ∀ w : List ℕ, w ≠ [] → (∀ k ∈ w, 1 ≤ k) →
      μ {x | digitPrefix (a x) w.length = w} ≤ (C : ℝ≥0∞) * ν (gaussCylinder w)) :
    Measure.map (gaussCode ∘ a) μ ≤ C • ν := by
  apply gaussCode_map_le_of_cylinder_bounds μ (C • ν) a ha
  intro w hwne hw
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] using hbound w hwne hw

theorem gaussCode_map_absolutelyContinuous {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [ν.OuterRegular] (a : X → ℕ → ℕ+)
    (ha : Measurable a) (C : ℝ≥0)
    (hbound : ∀ w : List ℕ, w ≠ [] → (∀ k ∈ w, 1 ≤ k) →
      μ {x | digitPrefix (a x) w.length = w} ≤ (C : ℝ≥0∞) * ν (gaussCylinder w)) :
    Measure.map (gaussCode ∘ a) μ ≪ ν := by
  intro s hs
  have h := Measure.le_iff'.mp (gaussCode_map_le_smul_of_cylinder_bounds μ ν a ha C hbound) s
  simpa only [Measure.smul_apply, hs, smul_zero, nonpos_iff_eq_zero] using h

end

end BianchiIX
