import BianchiIX.Statistics.GaussDensity

/-! Countable stopping losses with no normalization by the surviving terminal domain. -/

namespace BianchiIX

noncomputable section

open Set MeasureTheory
open scoped ENNReal

theorem finite_distortion_budget_le (d e : ℕ → ℝ)
    (hd0 : ∀ j, 0 ≤ d j) (he0 : ∀ j, 0 ≤ e j) (hd : Summable d) (he : Summable e) (n : ℕ) :
    (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤
      (∑' j, e j) + 2 * ∑' j, d (j + 1) := by
  let f := fun j => e j + if j = 0 then 0 else 2 * d j
  have hds : Summable (fun j => d (j + 1)) := (summable_nat_add_iff 1).mpr hd
  have hes : Summable (fun j => e (j + 1)) := (summable_nat_add_iff 1).mpr he
  have hfs : Summable (fun j => f (j + 1)) := by
    simpa only [f, Nat.add_one_ne_zero, if_false] using hes.add (hds.mul_left 2)
  have hf : Summable f := (summable_nat_add_iff 1).mp hfs
  have htail : (∑' j, f (j + 1)) = (∑' j, e (j + 1)) + 2 * ∑' j, d (j + 1) := by
    simp only [f, Nat.add_one_ne_zero, if_false]
    rw [hes.tsum_add (hds.mul_left 2), tsum_mul_left]
  have htotal : (∑' j, f j) = (∑' j, e j) + 2 * ∑' j, d (j + 1) := by
    rw [hf.tsum_eq_zero_add, htail, he.tsum_eq_zero_add]
    simp [f, add_assoc]
  rw [← htotal]
  apply hf.sum_le_tsum (Finset.range n)
  intro j _
  dsimp [f]
  split_ifs <;> linarith [hd0 j, he0 j]

theorem gaussCylinder_prefixes_disjoint {ι : Type*} (a : ι → ℕ → ℕ+) (n : ℕ)
    (hunique : Function.Injective (fun i => digitPrefix (a i) n)) :
    Pairwise (fun i j => Disjoint (gaussCylinder (digitPrefix (a i) n))
      (gaussCylinder (digitPrefix (a j) n))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hc := gaussCylinder_comparable (digitPrefix_positive (a i) n)
    (digitPrefix_positive (a j) n) ⟨x, hxi, hxj⟩
  have hlen : (digitPrefix (a i) n).length = (digitPrefix (a j) n).length := by
    simp only [digitPrefix_length]
  exact hij (hunique (hc.elim (fun h => h.eq_of_length hlen)
    (fun h => (h.eq_of_length hlen.symm).symm)))

theorem gaussCylinder_prefixes_tsum_le_one {ι : Type*} [Countable ι]
    (a : ι → ℕ → ℕ+) (n : ℕ)
    (hunique : Function.Injective (fun i => digitPrefix (a i) n)) :
    (∑' i, volume (gaussCylinder (digitPrefix (a i) n))) ≤ 1 := by
  rw [← measure_iUnion (gaussCylinder_prefixes_disjoint a n hunique)
    (fun i => measurableSet_gaussCylinder _)]
  calc
    volume (⋃ i, gaussCylinder (digitPrefix (a i) n)) ≤ volume (Ioo (0 : ℝ) 1) := by
      apply measure_mono
      apply iUnion_subset
      intro i x hx
      rcases hx with ⟨t, ht, rfl⟩
      exact gaussWord_mem_open_unit _ (digitPrefix_positive (a i) n) ht
    _ = 1 := by norm_num

def stoppedLayer {ι : Type*} (H : ι → ℝ → ℝ) (A : ι → Set ℝ) : Set ℝ :=
  ⋃ i, H i '' A i

theorem measurableSet_stoppedLayer {ι : Type*} [Countable ι]
    (H : ι → ℝ → ℝ) (A : ι → Set ℝ) (hA : ∀ i, MeasurableSet (A i))
    (hH : ∀ i, ContinuousOn (H i) (A i)) (hinj : ∀ i, InjOn (H i) (A i)) :
    MeasurableSet (stoppedLayer H A) :=
  MeasurableSet.iUnion (fun i => (hA i).image_of_continuousOn_injOn (hH i) (hinj i))

theorem stopped_node_mass_le (a : ℕ → ℕ+) (n : ℕ) {H : ℝ → ℝ}
    {A : Set ℝ} {L : ℝ} {ell : ℝ≥0∞} (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (0 : ℝ) 1)
    (hH : ∀ x ∈ A, DifferentiableAt ℝ H x) (hinj : InjOn H A) (hsize : volume A ≤ ell)
    (hbound : ∀ x ∈ A, |deriv H x| ≤ Real.exp L * |deriv (gaussWord (digitPrefix a n)) x|) :
    volume (H '' A) ≤ (2 * ENNReal.ofReal (Real.exp L) * ell) *
      volume (gaussCylinder (digitPrefix a n)) := by
  have htransport := gaussPrefix_image_measure_le a n hA (fun x hx => (hAsub hx).1.le) hH hinj hbound
  have hsmall := gaussPrefix_small_set_image_le a n hA hAsub
  calc
    volume (H '' A) ≤ ENNReal.ofReal (Real.exp L) *
        (2 * volume (gaussCylinder (digitPrefix a n)) * volume A) :=
      htransport.trans (mul_le_mul le_rfl hsmall (by positivity) (by positivity))
    _ ≤ ENNReal.ofReal (Real.exp L) *
        (2 * volume (gaussCylinder (digitPrefix a n)) * ell) := by gcongr
    _ = _ := by ring

theorem stopped_layer_mass_le {ι : Type*} [Countable ι]
    (a : ι → ℕ → ℕ+) (n : ℕ) (H : ι → ℝ → ℝ) (A : ι → Set ℝ)
    {L : ℝ} {ell : ℝ≥0∞}
    (hunique : Function.Injective (fun i => digitPrefix (a i) n))
    (hA : ∀ i, MeasurableSet (A i)) (hAsub : ∀ i, A i ⊆ Ioo (0 : ℝ) 1)
    (hH : ∀ i, ∀ x ∈ A i, DifferentiableAt ℝ (H i) x) (hinj : ∀ i, InjOn (H i) (A i))
    (hsize : ∀ i, volume (A i) ≤ ell)
    (hbound : ∀ i, ∀ x ∈ A i,
      |deriv (H i) x| ≤ Real.exp L * |deriv (gaussWord (digitPrefix (a i) n)) x|) :
    volume (stoppedLayer H A) ≤ 2 * ENNReal.ofReal (Real.exp L) * ell := by
  calc
    volume (stoppedLayer H A) ≤ ∑' i, volume (H i '' A i) := measure_iUnion_le _
    _ ≤ ∑' i, (2 * ENNReal.ofReal (Real.exp L) * ell) *
        volume (gaussCylinder (digitPrefix (a i) n)) :=
      ENNReal.tsum_le_tsum (fun i => stopped_node_mass_le (a i) n
        (hA i) (hAsub i) (hH i) (hinj i) (hsize i) (hbound i))
    _ = (2 * ENNReal.ofReal (Real.exp L) * ell) *
        ∑' i, volume (gaussCylinder (digitPrefix (a i) n)) := ENNReal.tsum_mul_left
    _ ≤ (2 * ENNReal.ofReal (Real.exp L) * ell) * 1 :=
      mul_le_mul le_rfl (gaussCylinder_prefixes_tsum_le_one a n hunique)
        (by positivity) (by positivity)
    _ = _ := mul_one _

theorem stopped_total_mass_le {ι : ℕ → Type*} [∀ m, Countable (ι m)]
    (a : ∀ m, ι m → ℕ → ℕ+) (H : ∀ m, ι m → ℝ → ℝ) (A : ∀ m, ι m → Set ℝ)
    (ell : ℕ → ℝ≥0∞) (L : ℝ)
    (hunique : ∀ m, Function.Injective (fun i => digitPrefix (a m i) m))
    (hA : ∀ m i, MeasurableSet (A m i)) (hAsub : ∀ m i, A m i ⊆ Ioo (0 : ℝ) 1)
    (hH : ∀ m i, ∀ x ∈ A m i, DifferentiableAt ℝ (H m i) x)
    (hinj : ∀ m i, InjOn (H m i) (A m i)) (hsize : ∀ m i, volume (A m i) ≤ ell m)
    (hbound : ∀ m i, ∀ x ∈ A m i,
      |deriv (H m i) x| ≤ Real.exp L * |deriv (gaussWord (digitPrefix (a m i) m)) x|) :
    volume (⋃ m, stoppedLayer (H m) (A m)) ≤
      2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m := by
  calc
    volume (⋃ m, stoppedLayer (H m) (A m)) ≤ ∑' m, volume (stoppedLayer (H m) (A m)) :=
      measure_iUnion_le _
    _ ≤ ∑' m, 2 * ENNReal.ofReal (Real.exp L) * ell m :=
      ENNReal.tsum_le_tsum (fun m => stopped_layer_mass_le (a m) m (H m) (A m)
        (hunique m) (hA m) (hAsub m) (hH m) (hinj m) (hsize m) (hbound m))
    _ = _ := ENNReal.tsum_mul_left

/-- The cumulative distortion enters only through its already proved finite-prefix bound. -/
theorem stopped_total_mass_le_of_branches {ι : ℕ → Type*} [∀ m, Countable (ι m)]
    (a : ∀ m, ι m → ℕ → ℕ+) (h : ∀ m, ι m → ℕ → ℝ → ℝ)
    (D Y : ∀ m, ι m → ℝ → ℕ → ℝ) (A : ∀ m, ι m → Set ℝ)
    (d e : ℕ → ℝ) (ell : ℕ → ℝ≥0∞) (L : ℝ)
    (hbudget : ∀ m, (∑ j ∈ Finset.range m, (e j + if j = 0 then 0 else 2 * d j)) ≤ L)
    (hunique : ∀ m, Function.Injective (fun i => digitPrefix (a m i) m))
    (hA : ∀ m i, MeasurableSet (A m i)) (hAsub : ∀ m i, A m i ⊆ Ioo (0 : ℝ) 1)
    (hinj : ∀ m i, InjOn (branchPrefix (h m i) m) (A m i))
    (hsize : ∀ m i, volume (A m i) ≤ ell m)
    (hterminal : ∀ m i, ∀ t ∈ A m i, Y m i t m = t)
    (hrec : ∀ m i, ∀ t ∈ A m i, ∀ j < m, h m i j (Y m i t (j + 1)) = Y m i t j)
    (hder : ∀ m i, ∀ t ∈ A m i, ∀ j < m,
      HasDerivAt (h m i j) (D m i t j) (Y m i t (j + 1)))
    (hy : ∀ m i, ∀ t ∈ A m i, ∀ j ≤ m, 0 ≤ Y m i t j)
    (hD : ∀ m i, ∀ t ∈ A m i, ∀ j < m, D m i t j ≠ 0)
    (hvalue : ∀ m i, ∀ t ∈ A m i, ∀ j < m,
      |h m i j (Y m i t (j + 1)) - gaussInv (a m i j) (Y m i t (j + 1))| ≤ d j)
    (hlog : ∀ m i, ∀ t ∈ A m i, ∀ j < m,
      |Real.log (|D m i t j| / |deriv (gaussInv (a m i j)) (Y m i t (j + 1))|)| ≤ e j) :
    volume (⋃ m, stoppedLayer (fun i => branchPrefix (h m i) m) (A m)) ≤
      2 * ENNReal.ofReal (Real.exp L) * ∑' m, ell m := by
  apply stopped_total_mass_le a (fun m i => branchPrefix (h m i) m) A ell L
    hunique hA hAsub
  · intro m i t ht
    have hd := hasDerivAt_branchPrefix (h m i) (D m i t) (Y m i t) m
      (hrec m i t ht) (hder m i t ht)
    rw [hterminal m i t ht] at hd
    exact hd.differentiableAt
  · exact hinj
  · exact hsize
  · intro m i t ht
    have hb := gauss_actual_prefix_deriv_bound (a m i) (h m i) (D m i t) (Y m i t) d e m
      (hrec m i t ht) (hder m i t ht) (hy m i t ht) (hD m i t ht)
      (hvalue m i t ht) (hlog m i t ht)
    rw [hterminal m i t ht] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbudget m)) (abs_nonneg _))

theorem stoppedLayer_restrict {ι : Type*} (H : ι → ℝ → ℝ) (A : ι → Set ℝ) (I : Set ℝ) :
    stoppedLayer H (fun i => A i ∩ H i ⁻¹' I) = I ∩ stoppedLayer H A := by
  ext x
  simp only [stoppedLayer, mem_iUnion, mem_image, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨i, y, ⟨hy, hI⟩, rfl⟩
    exact ⟨hI, i, y, hy, rfl⟩
  · rintro ⟨hI, i, y, hy, rfl⟩
    exact ⟨i, y, ⟨hy, hI⟩, rfl⟩

theorem restricted_stopped_mass_le {I F : Set ℝ} {B : ℝ≥0∞} (hF : volume F ≤ B) :
    volume (I ∩ F) ≤ min (volume I) B :=
  le_min (measure_mono inter_subset_left) ((measure_mono inter_subset_right).trans hF)

def survivingSet {X : Type*} (K : ℕ → Set X) : Set X := ⋂ m, K m

def firstStoppedSet {X : Type*} (K : ℕ → Set X) (m : ℕ) : Set X := K m \ K (m + 1)

theorem measurableSet_survivingSet {X : Type*} [MeasurableSpace X]
    (K : ℕ → Set X) (hK : ∀ m, MeasurableSet (K m)) : MeasurableSet (survivingSet K) :=
  MeasurableSet.iInter hK

theorem measurableSet_firstStoppedSet {X : Type*} [MeasurableSpace X]
    (K : ℕ → Set X) (hK : ∀ m, MeasurableSet (K m)) (m : ℕ) :
    MeasurableSet (firstStoppedSet K m) := (hK m).diff (hK (m + 1))

theorem root_sdiff_survivingSet {X : Type*} (K : ℕ → Set X) (hK : Antitone K) :
    K 0 \ survivingSet K = ⋃ m, firstStoppedSet K m := by
  classical
  ext x
  simp only [survivingSet, firstStoppedSet, mem_sdiff, mem_iInter, not_forall, mem_iUnion]
  constructor
  · rintro ⟨h0, hex⟩
    have hN := Nat.find_spec hex
    have hNpos : 0 < Nat.find hex := by
      by_contra h
      have hz : Nat.find hex = 0 := by omega
      exact hN (hz ▸ h0)
    refine ⟨Nat.find hex - 1, ?_, ?_⟩
    · by_contra hprev
      exact Nat.find_min hex (by omega) hprev
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] using hN
  · rintro ⟨m, hm, hn⟩
    exact ⟨hK (Nat.zero_le m) hm, m + 1, hn⟩

theorem firstStoppedSet_restrict {X : Type*} (K : ℕ → Set X) (I : Set X) (m : ℕ) :
    firstStoppedSet (fun n => I ∩ K n) m = I ∩ firstStoppedSet K m := by
  ext x
  simp only [firstStoppedSet, mem_sdiff, mem_inter_iff]
  tauto

theorem survivingSet_restrict {X : Type*} (K : ℕ → Set X) (I : Set X) :
    survivingSet (fun n => I ∩ K n) = I ∩ survivingSet K := by
  ext x
  simp only [survivingSet, mem_iInter, mem_inter_iff, forall_and]
  simp

theorem restricted_survivor_loss_le {K : ℕ → Set ℝ} (hK : Antitone K)
    {I : Set ℝ} {B : ℝ≥0∞} (hstop : volume (⋃ m, firstStoppedSet K m) ≤ B) :
    volume ((I ∩ K 0) \ survivingSet (fun n => I ∩ K n)) ≤ min (volume I) B := by
  rw [survivingSet_restrict]
  have heq : (I ∩ K 0) \ (I ∩ survivingSet K) = I ∩ (K 0 \ survivingSet K) := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [heq, root_sdiff_survivingSet K hK]
  exact restricted_stopped_mass_le hstop

end

end BianchiIX
