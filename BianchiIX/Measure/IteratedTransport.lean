import BianchiIX.Measure.ReturnIterates
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem map_weighted_restrict_of_image_measure {R : X → X} {D S : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R)
    (hchange : ∀ A, MeasurableSet A → A ⊆ D → μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    (hS : MeasurableSet S) (hSD : S ⊆ D) :
    ((μ.restrict S).withDensity j).map R = μ.restrict (R '' S) := by
  ext A hA
  rw [Measure.map_apply hR hA, withDensity_apply _ (hA.preimage hR),
    Measure.restrict_restrict (hA.preimage hR), Measure.restrict_apply hA,
    ← hchange _ ((hA.preimage hR).inter hS) (inter_subset_right.trans hSD)]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxA, hxS⟩, rfl⟩
    exact ⟨hxA, x, hxS, rfl⟩
  · rintro ⟨hyA, x, hxS, rfl⟩
    exact ⟨x, ⟨hyA, hxS⟩, rfl⟩

theorem setLIntegral_image_of_image_measure {R : X → X} {D S : Set X} {j g : X → ℝ≥0∞}
    (hR : Measurable R) (hj : Measurable j) (hg : Measurable g)
    (hchange : ∀ A, MeasurableSet A → A ⊆ D → μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    (hS : MeasurableSet S) (hSD : S ⊆ D) :
    ∫⁻ y in R '' S, g y ∂μ = ∫⁻ x in S, j x * g (R x) ∂μ := by
  rw [← map_weighted_restrict_of_image_measure hR hchange hS hSD,
    lintegral_map hg hR]
  exact lintegral_withDensity_eq_lintegral_mul _ hj (hg.comp hR)

/-- Set transport alone implies the full finite product formula, with no finite-measure assumption. -/
theorem measure_image_finiteReturnIterate {R : X → X} {D : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hj : Measurable j)
    (hchange : ∀ S, MeasurableSet S → S ⊆ D →
      MeasurableSet (R '' S) ∧ μ (R '' S) = ∫⁻ x in S, j x ∂μ) (n : ℕ) :
    ∀ S, MeasurableSet S → S ⊆ finiteReturnDomain R D n →
      MeasurableSet ((R^[n]) '' S) ∧
        μ ((R^[n]) '' S) = ∫⁻ x in S, finiteReturnJacobian R j n x ∂μ := by
  induction n with
  | zero => intro S hS _; simpa using hS
  | succ n ih =>
    intro S hS hSD
    have hSn : S ⊆ finiteReturnDomain R D n :=
      hSD.trans (finiteReturnDomain_antitone R D (Nat.le_succ n))
    have htarget : (R^[n]) '' S ⊆ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hSD hx n (Nat.lt_succ_self n)
    have hstep := hchange _ (ih S hS hSn).1 htarget
    have himage : (R^[n + 1]) '' S = R '' ((R^[n]) '' S) := by
      rw [← image_comp]
      congr 1
      funext x
      exact Function.iterate_succ_apply' R n x
    refine ⟨himage ▸ hstep.1, ?_⟩
    rw [himage, hstep.2,
      setLIntegral_image_of_image_measure (hR.iterate n) (measurable_finiteReturnJacobian hR hj n)
        hj (fun T hT hTD => (ih T hT hTD).2) hS hSn]
    exact lintegral_congr fun x => (finiteReturnJacobian_succ R j n x).symm

theorem setLIntegral_finiteReturnIterate {R : X → X} {D S : Set X} {j g : X → ℝ≥0∞}
    (hR : Measurable R) (hj : Measurable j) (hg : Measurable g)
    (hchange : ∀ A, MeasurableSet A → A ⊆ D →
      MeasurableSet (R '' A) ∧ μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    (n : ℕ) (hS : MeasurableSet S) (hSD : S ⊆ finiteReturnDomain R D n) :
    ∫⁻ y in (R^[n]) '' S, g y ∂μ =
      ∫⁻ x in S, finiteReturnJacobian R j n x * g (R^[n] x) ∂μ :=
  setLIntegral_image_of_image_measure (hR.iterate n) (measurable_finiteReturnJacobian hR hj n) hg
    (fun A hA hAD => (measure_image_finiteReturnIterate hR hj hchange n A hA hAD).2) hS hSD

theorem measure_le_finiteReturn_image {R : X → X} {D S : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hj : Measurable j) (hexpand : ∀ x ∈ D, 1 ≤ j x)
    (hchange : ∀ A, MeasurableSet A → A ⊆ D →
      MeasurableSet (R '' A) ∧ μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    (n : ℕ) (hS : MeasurableSet S) (hSD : S ⊆ finiteReturnDomain R D n) :
    μ S ≤ μ ((R^[n]) '' S) := by
  rw [(measure_image_finiteReturnIterate hR hj hchange n S hS hSD).2]
  have H := lintegral_mono_ae (μ := μ.restrict S)
    (f := fun _ : X => (1 : ℝ≥0∞)) (g := finiteReturnJacobian R j n)
    (ae_restrict_of_forall_mem hS (fun x hx => one_le_finiteReturnJacobian hexpand (hSD hx)))
  simpa using H

theorem finiteReturn_image_null_iff {R : X → X} {D S : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hj : Measurable j) (hexpand : ∀ x ∈ D, 1 ≤ j x)
    (hchange : ∀ A, MeasurableSet A → A ⊆ D →
      MeasurableSet (R '' A) ∧ μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    (n : ℕ) (hS : MeasurableSet S) (hSD : S ⊆ finiteReturnDomain R D n) :
    μ ((R^[n]) '' S) = 0 ↔ μ S = 0 := by
  constructor
  · intro hz
    exact le_antisymm (hz ▸ measure_le_finiteReturn_image hR hj hexpand hchange n hS hSD) bot_le
  · intro hz
    have hμ : μ.restrict S = 0 := by simpa using hz
    rw [(measure_image_finiteReturnIterate hR hj hchange n S hS hSD).2, hμ, lintegral_zero_measure]

theorem finiteReturn_preimage_null {R : X → X} {D Z : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hD : MeasurableSet D) (hj : Measurable j) (hexpand : ∀ x ∈ D, 1 ≤ j x)
    (hchange : ∀ A, MeasurableSet A → A ⊆ D →
      MeasurableSet (R '' A) ∧ μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    (hZ : MeasurableSet Z) (hnull : μ Z = 0) (n : ℕ) :
    μ (finiteReturnDomain R D n ∩ (R^[n]) ⁻¹' Z) = 0 := by
  apply (finiteReturn_image_null_iff hR hj hexpand hchange n
    ((measurableSet_finiteReturnDomain hR hD n).inter (hZ.preimage (hR.iterate n))) inter_subset_left).mp
  exact measure_mono_null (by rintro _ ⟨x, hx, rfl⟩; exact hx.2) hnull

theorem measure_finiteReturn_image_strict {R : X → X} {D S : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hj : Measurable j) (hexpand : ∀ x ∈ D, 1 < j x)
    (hchange : ∀ A, MeasurableSet A → A ⊆ D →
      MeasurableSet (R '' A) ∧ μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    {n : ℕ} (hn : 0 < n) (hS : MeasurableSet S) (hSD : S ⊆ finiteReturnDomain R D n)
    (hfinite : μ S ≠ ∞) (hpos : μ S ≠ 0) : μ S < μ ((R^[n]) '' S) := by
  rw [(measure_image_finiteReturnIterate hR hj hchange n S hS hSD).2]
  have hμ : μ.restrict S ≠ 0 := by simpa using hpos
  have H := lintegral_strict_mono (f := fun _ : X => (1 : ℝ≥0∞)) hμ
    (measurable_finiteReturnJacobian hR hj n).aemeasurable (by simpa using hfinite)
    (ae_restrict_of_forall_mem hS (fun x hx => one_lt_finiteReturnJacobian hexpand hn (hSD hx)))
  simpa using H

theorem ae_avoids_null_finiteReturns {R : X → X} {D Z : Set X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hD : MeasurableSet D) (hj : Measurable j) (hexpand : ∀ x ∈ D, 1 ≤ j x)
    (hchange : ∀ A, MeasurableSet A → A ⊆ D →
      MeasurableSet (R '' A) ∧ μ (R '' A) = ∫⁻ x in A, j x ∂μ)
    (hZ : MeasurableSet Z) (hnull : μ Z = 0) :
    ∀ᵐ x ∂μ, ∀ n, x ∈ finiteReturnDomain R D n → R^[n] x ∉ Z := by
  apply ae_all_iff.mpr
  intro n
  have H := finiteReturn_preimage_null hR hD hj hexpand hchange hZ hnull n
  rw [ae_iff]
  convert! H using 1
  congr 1
  ext x
  simp

end BianchiIX
