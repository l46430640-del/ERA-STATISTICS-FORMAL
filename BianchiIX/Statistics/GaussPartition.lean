import BianchiIX.Statistics.GaussTypical
import BianchiIX.Statistics.EmpiricalMass

/-! Fixed-depth Gauss partitions and convergence of their empirical probability masses. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace BianchiIX

noncomputable section

abbrev GaussWords (n : ℕ) := {w : List ℕ // w.length = n ∧ ∀ k ∈ w, 1 ≤ k}

def gaussPrefixWord (a : ℕ → ℕ+) (n : ℕ) : GaussWords n :=
  ⟨digitPrefix a n, digitPrefix_length a n, digitPrefix_positive a n⟩

def gaussMass (n : ℕ) (w : GaussWords n) : ℝ := (gaussMeasure (gaussCylinder w.val)).toReal

theorem gaussWords_disjoint (n : ℕ) :
    Pairwise (fun v w : GaussWords n => Disjoint (gaussCylinder v.val) (gaussCylinder w.val)) := by
  intro v w hvw
  apply disjoint_left.mpr
  intro x hxv hxw
  have hc := gaussCylinder_comparable v.property.2 w.property.2 ⟨x, hxv, hxw⟩
  have hlen := v.property.1.trans w.property.1.symm
  exact hvw (Subtype.ext (hc.elim (fun h => h.eq_of_length hlen)
    (fun h => (h.eq_of_length hlen.symm).symm)))

theorem gaussWords_cover (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hi : Irrational x) :
    x ∈ ⋃ w : GaussWords n, gaussCylinder w.val := by
  obtain ⟨a, rfl⟩ := exists_gaussCode_of_irrational hx hi
  exact mem_iUnion.mpr ⟨gaussPrefixWord a n, gaussCode_mem_cylinder a n⟩

theorem ae_gaussWords_cover (n : ℕ) :
    ∀ᵐ x ∂gaussMeasure, x ∈ ⋃ w : GaussWords n, gaussCylinder w.val := by
  filter_upwards [ae_gaussMeasure_mem_unit, ae_gaussMeasure_irrational] with x hx hi
  exact gaussWords_cover n hx hi

theorem gaussWords_mass_sum (n : ℕ) :
    (∑' w : GaussWords n, gaussMeasure (gaussCylinder w.val)) = 1 := by
  rw [← measure_iUnion (gaussWords_disjoint n) (fun w => measurableSet_gaussCylinder w.val)]
  have heq : (⋃ w : GaussWords n, gaussCylinder w.val) =ᵐ[gaussMeasure] univ := by
    filter_upwards [ae_gaussWords_cover n] with x hx
    exact propext (iff_true_intro hx)
  simpa only [gaussMeasure_univ] using measure_congr heq

theorem gaussMass_nonneg (n : ℕ) (w : GaussWords n) : 0 ≤ gaussMass n w := ENNReal.toReal_nonneg

theorem gaussMass_hasSum (n : ℕ) : HasSum (gaussMass n) 1 := by
  have hsum : (∑' w : GaussWords n, gaussMeasure (gaussCylinder w.val)) ≠ ⊤ := by
    rw [gaussWords_mass_sum]
    exact ENNReal.one_ne_top
  have h := ENNReal.hasSum_toReal hsum
  rw [← ENNReal.tsum_toReal_eq (fun w : GaussWords n =>
      measure_ne_top gaussMeasure (gaussCylinder w.val)),
    gaussWords_mass_sum, ENNReal.toReal_one] at h
  exact h

def gaussEmpiricalMass (a : ℕ → ℕ+) (n N : ℕ) : GaussWords n → ℝ :=
  empiricalMass (fun j => gaussPrefixWord (shiftDigits a j) n) N

theorem gaussEmpiricalMass_eq_average (a : ℕ → ℕ+) (n N : ℕ) (w : GaussWords n) :
    gaussEmpiricalMass a n N w =
      birkhoffAverage ℝ gaussMap (gaussCylinderObservable w.val) (N + 1) (gaussCode a) := by
  classical
  change ((N + 1 : ℕ) : ℝ)⁻¹ * _ = ((N + 1 : ℕ) : ℝ)⁻¹ * _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussMap_iterate_code, gaussCylinderObservable_code _ w.val w.property.2]
  simp only [gaussPrefixWord, Subtype.ext_iff, w.property.1, eq_comm]

theorem gaussEmpiricalMass_tendsto (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (n : ℕ) (w : GaussWords n) :
    Tendsto (fun N => gaussEmpiricalMass a n N w) atTop (𝓝 (gaussMass n w)) := by
  simp_rw [gaussEmpiricalMass_eq_average]
  exact (gaussCylinder_average_of_typical ha w.val).comp (tendsto_add_atTop_nat 1)

theorem gaussEmpiricalMass_l1_tendsto (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (n : ℕ) :
    Tendsto (fun N => ∑' w : GaussWords n, |gaussEmpiricalMass a n N w - gaussMass n w|)
      atTop (𝓝 0) :=
  probability_mass_l1_tendsto (fun N w => empiricalMass_nonneg _ N w) (gaussMass_nonneg n)
    (fun N => empiricalMass_hasSum _ N) (gaussMass_hasSum n) (gaussEmpiricalMass_tendsto a ha n)

theorem gaussEmpiricalMass_weighted_tendsto (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (n : ℕ) {f : GaussWords n → ℝ} {M : ℝ} (hf : ∀ w, |f w| ≤ M) :
    Tendsto (fun N => ∑' w, gaussEmpiricalMass a n N w * f w)
      atTop (𝓝 (∑' w, gaussMass n w * f w)) :=
  probability_weighted_tendsto (fun N w => empiricalMass_nonneg _ N w) (gaussMass_nonneg n)
    (fun N => empiricalMass_hasSum _ N) (gaussMass_hasSum n) (gaussEmpiricalMass_tendsto a ha n) hf

end
end BianchiIX
