import BianchiIX.Statistics.GaussTransfer
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! The inverse-branch partition and invariance of the concrete Gauss probability measure. -/

open Set MeasureTheory
open scoped ENNReal

namespace BianchiIX

theorem measurable_gaussMap : Measurable gaussMap :=
  (measurable_const.div measurable_id).fract

theorem gaussMap_inverse {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (j : ℕ) :
    gaussMap (gaussInv ((j : ℝ) + 1) x) = x := by
  unfold gaussMap gaussInv
  rw [one_div_one_div]
  have h := Int.fract_natCast_add (j + 1) x
  push_cast at h
  rw [h, Int.fract_eq_self.mpr ⟨hx.1.le, hx.2⟩]

theorem gaussMap_irrational {x : ℝ} (hx : Irrational x) : Irrational (gaussMap x) := by
  simpa only [gaussMap, Int.fract, one_div] using hx.inv.sub_intCast ⌊1 / x⌋

theorem gaussMap_mem_unit {x : ℝ} (hx : Irrational x) : gaussMap x ∈ Ioo (0 : ℝ) 1 :=
  ⟨lt_of_le_of_ne (Int.fract_nonneg _) (gaussMap_irrational hx).ne_zero.symm,
    Int.fract_lt_one _⟩

theorem exists_gauss_inverse {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∃ j : ℕ, gaussInv ((j : ℝ) + 1) (gaussMap x) = x := by
  have hinv : 0 < 1 / x := one_div_pos.mpr hx.1
  have hk : 1 ≤ ⌊1 / x⌋₊ := Nat.one_le_floor_iff _ |>.mpr
    ((le_div_iff₀ hx.1).mpr (by linarith [hx.2]))
  refine ⟨⌊1 / x⌋₊ - 1, ?_⟩
  have hcast : ((⌊1 / x⌋₊ - 1 : ℕ) : ℝ) + 1 = (⌊1 / x⌋ : ℤ) := by
    rw [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel,
      natCast_floor_eq_intCast_floor hinv.le]
  rw [gaussInv, hcast, gaussMap, Int.floor_add_fract, one_div_one_div]

theorem gauss_inverse_images_disjoint {A : Set ℝ} (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    Pairwise (fun i j : ℕ => Disjoint
      (gaussInv ((i : ℝ) + 1) '' A) (gaussInv ((j : ℝ) + 1) '' A)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
  have hxy : x = y := by
    have h := congrArg gaussMap (hxz.trans hyz.symm)
    simpa only [gaussMap_inverse (hsub hx), gaussMap_inverse (hsub hy)] using h
  subst y
  have heq := congrArg (fun t : ℝ => 1 / t) (hxz.trans hyz.symm)
  simp only [gaussInv, one_div_one_div] at heq
  have hcast : (i : ℝ) = j := by linarith
  exact hij (by exact_mod_cast hcast)

theorem gaussMap_preimage_ae (A : Set ℝ) :
    gaussMap ⁻¹' A =ᵐ[gaussMeasure]
      ⋃ j : ℕ, gaussInv ((j : ℝ) + 1) '' (A ∩ Ioo (0 : ℝ) 1) := by
  filter_upwards [ae_gaussMeasure_mem_unit, ae_gaussMeasure_irrational] with x hx hi
  apply propext
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_gauss_inverse hx
    exact mem_iUnion.mpr ⟨j, gaussMap x, ⟨h, gaussMap_mem_unit hi⟩, hj⟩
  · intro h
    rcases mem_iUnion.mp h with ⟨j, y, hy, rfl⟩
    change gaussMap (gaussInv ((j : ℝ) + 1) y) ∈ A
    rw [gaussMap_inverse hy.2]
    exact hy.1

theorem measurePreserving_gaussMap : MeasurePreserving gaussMap gaussMeasure gaussMeasure := by
  refine ⟨measurable_gaussMap, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_gaussMap hA,
    measure_congr (gaussMap_preimage_ae A),
    measure_iUnion (gauss_inverse_images_disjoint inter_subset_right)
      (fun j => (measurableEmbedding_gaussInv _).measurableSet_image.mpr
        (hA.inter measurableSet_Ioo)),
    gaussMeasure_inverse_sum (hA.inter measurableSet_Ioo) inter_subset_right]
  apply measure_congr
  filter_upwards [ae_gaussMeasure_mem_unit] with x hx
  change (x ∈ A ∩ Ioo (0 : ℝ) 1) = (x ∈ A)
  exact propext (and_iff_left hx)

end BianchiIX
