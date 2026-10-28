import BianchiIX.Analysis.RootCurveExtension
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

/-- Adjacent interior samples recover even a one-sided derivative. -/
theorem tendsto_adjacent_secant {f : ℝ → ℝ} {d x : ℝ} {S : Set ℝ} {h : ℕ → ℝ}
    (hf : HasDerivWithinAt f d S x) (ht : Tendsto h atTop (𝓝 0))
    (hn : ∀ n, h n ≠ 0) (h₁ : ∀ n, x + h n ∈ S) (h₂ : ∀ n, x + 2 * h n ∈ S) :
    Tendsto (fun n => (f (x + 2 * h n) - f (x + h n)) / h n) atTop (𝓝 d) := by
  have ht₁ : Tendsto (fun n => x + h n) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add ht
  have ht₂ : Tendsto (fun n => x + 2 * h n) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (ht.const_mul 2)
  have hs₁ : Tendsto (fun n => x + h n) atTop (𝓝[S \ {x}] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht₁, Eventually.of_forall fun n => ⟨h₁ n, ?_⟩⟩
    simpa using hn n
  have hs₂ : Tendsto (fun n => x + 2 * h n) atTop (𝓝[S \ {x}] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨ht₂, Eventually.of_forall fun n => ⟨h₂ n, ?_⟩⟩
    simpa using hn n
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hf
  have H := ((hs.comp hs₂).const_mul 2).sub (hs.comp hs₁)
  convert! H using 1
  · ext n
    dsimp only [Function.comp_def]
    rw [slope_def_field, slope_def_field]
    simp only [add_sub_cancel_left]
    field_simp [hn n]
    ring
  · congr 1
    ring

/-- The sign points into the interval, including at its right endpoint. -/
def curveSampleStep (l r x : ℝ) (n : ℕ) : ℝ :=
  (if x < r then r - x else l - x) / (3 * ((n : ℝ) + 1))

theorem curveSampleStep_samples {l r x : ℝ} (hlr : l < r) (hx : x ∈ Icc l r) (n : ℕ) :
    curveSampleStep l r x n ≠ 0 ∧
      x + curveSampleStep l r x n ∈ Ioo l r ∧
      x + 2 * curveSampleStep l r x n ∈ Ioo l r := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < 3 * ((n : ℝ) + 1) := by positivity
  unfold curveSampleStep
  by_cases hxr : x < r
  · rw [if_pos hxr]
    have hp : 0 < (r - x) / (3 * ((n : ℝ) + 1)) := div_pos (sub_pos.mpr hxr) hden
    have hb : 2 * ((r - x) / (3 * ((n : ℝ) + 1))) < r - x := by
      rw [← mul_div_assoc, div_lt_iff₀ hden]
      nlinarith
    exact ⟨ne_of_gt hp, ⟨by linarith [hx.1], by linarith⟩,
      ⟨by linarith [hx.1], by linarith⟩⟩
  · rw [if_neg hxr]
    have hxe : x = r := le_antisymm hx.2 (le_of_not_gt hxr)
    have hp : (l - x) / (3 * ((n : ℝ) + 1)) < 0 :=
      div_neg_of_neg_of_pos (by linarith) hden
    have hb : l - x < 2 * ((l - x) / (3 * ((n : ℝ) + 1))) := by
      rw [← mul_div_assoc, lt_div_iff₀ hden]
      nlinarith
    exact ⟨ne_of_lt hp, ⟨by linarith, by linarith [hx.2]⟩,
      ⟨by linarith, by linarith [hx.2]⟩⟩

theorem tendsto_curveSampleStep (l r x : ℝ) :
    Tendsto (curveSampleStep l r x) atTop (𝓝 0) := by
  have H := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    ((if x < r then r - x else l - x) / 3)
  unfold curveSampleStep
  simpa only [mul_zero, div_mul_eq_div_div, mul_one_div] using H

theorem measurable_curveSampleStep {X : Type*} [MeasurableSpace X]
    {l r x : X → ℝ} (hl : Measurable l) (hr : Measurable r) (hx : Measurable x) (n : ℕ) :
    Measurable (fun q => curveSampleStep (l q) (r q) (x q) n) :=
  (Measurable.ite (measurableSet_lt hx hr) (hr.sub hx) (hl.sub hx)).div_const _

/-- Interior Borel values determine measurable values and derivatives at every
measurable selector of the closed interval. No endpoint measurability is assumed. -/
theorem measurable_curve_selector {X : Type*} [MeasurableSpace X]
    {l r x : X → ℝ} {f df : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hx : Measurable x)
    (hlr : ∀ q, l q < r q) (hxi : ∀ q, x q ∈ Icc (l q) (r q))
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then f p.1 p.2 else 0))
    (hf : ∀ q y, y ∈ Icc (l q) (r q) →
      HasDerivWithinAt (f q) (df q y) (Icc (l q) (r q)) y) :
    Measurable (fun q => f q (x q)) ∧ Measurable (fun q => df q (x q)) := by
  let h : X → ℕ → ℝ := fun q => curveSampleStep (l q) (r q) (x q)
  have hsample q n := curveSampleStep_samples (hlr q) (hxi q) n
  have hm₁ (n : ℕ) : Measurable (fun q => f q (x q + h q n)) := by
    have H := hm.comp (measurable_id.prodMk (hx.add (measurable_curveSampleStep hl hr hx n)))
    convert! H using 1
    ext q
    exact (if_pos (hsample q n).2.1).symm
  have hm₂ (n : ℕ) : Measurable (fun q => f q (x q + 2 * h q n)) := by
    have H := hm.comp (measurable_id.prodMk
      (hx.add ((measurable_curveSampleStep hl hr hx n).const_mul 2)))
    convert! H using 1
    ext q
    exact (if_pos (hsample q n).2.2).symm
  constructor
  · apply measurable_of_tendsto_metrizable hm₁
    apply tendsto_pi_nhds.mpr
    intro q
    apply (hf q (x q) (hxi q)).continuousWithinAt.tendsto.comp
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa using tendsto_const_nhds.add (tendsto_curveSampleStep (l q) (r q) (x q))
    · exact ⟨(hsample q n).2.1.1.le, (hsample q n).2.1.2.le⟩
  · apply measurable_of_tendsto_metrizable
      (fun n => ((hm₂ n).sub (hm₁ n)).div (measurable_curveSampleStep hl hr hx n))
    apply tendsto_pi_nhds.mpr
    intro q
    exact tendsto_adjacent_secant (hf q (x q) (hxi q))
      (tendsto_curveSampleStep (l q) (r q) (x q))
      (fun n => (hsample q n).1)
      (fun n => ⟨(hsample q n).2.1.1.le, (hsample q n).2.1.2.le⟩)
      (fun n => ⟨(hsample q n).2.2.1.le, (hsample q n).2.2.2.le⟩)

/-- Recover the endpoint data before extending the curve. The arbitrary values
of the original functions outside their intervals play no role. -/
theorem measurable_rootCurve_of_interior {X : Type*} [MeasurableSpace X]
    {l r x : X → ℝ} {f df : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hx : Measurable x)
    (hlr : ∀ q, l q < r q)
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then f p.1 p.2 else 0))
    (hf : ∀ q y, y ∈ Icc (l q) (r q) →
      HasDerivWithinAt (f q) (df q y) (Icc (l q) (r q)) y) :
    Measurable (fun q => rootCurveExtension (l q) (r q) (f q) (df q) (x q)) ∧
      Measurable (fun q => rootCurveDerivative (l q) (r q) (f q) (df q) (x q)) := by
  classical
  obtain ⟨hfl, hdl⟩ := measurable_curve_selector hl hr hl hlr
    (fun q => ⟨le_rfl, (hlr q).le⟩) hm hf
  obtain ⟨hfr, hdr⟩ := measurable_curve_selector hl hr hr hlr
    (fun q => ⟨(hlr q).le, le_rfl⟩) hm hf
  let z : X → ℝ := fun q => max (l q) (min (x q) (r q))
  have hz : Measurable z := hl.max (hx.min hr)
  have hzi q : z q ∈ Icc (l q) (r q) :=
    ⟨le_max_left _ _, max_le (hlr q).le (min_le_right _ _)⟩
  obtain ⟨hfm, hdm⟩ := measurable_curve_selector hl hr hz hlr hzi hm hf
  have heq q (h₁ : ¬x q < l q) (h₂ : ¬r q < x q) : z q = x q := by
    simp only [z, min_eq_left (le_of_not_gt h₂), max_eq_right (le_of_not_gt h₁)]
  constructor
  · have H : Measurable (fun q =>
        if x q < l q then rootExtension (f q (l q)) (df q (l q)) (-1) (x q - l q)
        else if r q < x q then rootExtension (f q (r q)) (df q (r q)) 1 (x q - r q)
        else f q (z q)) :=
      Measurable.ite (measurableSet_lt hx hl)
        (measurable_rootExtension hfl hdl measurable_const (hx.sub hl))
        (Measurable.ite (measurableSet_lt hr hx)
          (measurable_rootExtension hfr hdr measurable_const (hx.sub hr)) hfm)
    convert! H using 1
    ext q
    unfold rootCurveExtension
    split_ifs with h₁ h₂
    · rfl
    · rfl
    · rw [heq q h₁ h₂]
  · have H : Measurable (fun q =>
        if x q < l q then df q (l q) * rootCutoff (-(x q - l q) / f q (l q))
        else if r q < x q then df q (r q) * rootCutoff ((x q - r q) / f q (r q))
        else df q (z q)) :=
      Measurable.ite (measurableSet_lt hx hl)
        (hdl.mul (continuous_rootCutoff.measurable.comp ((hx.sub hl).neg.div hfl)))
        (Measurable.ite (measurableSet_lt hr hx)
          (hdr.mul (continuous_rootCutoff.measurable.comp ((hx.sub hr).div hfr))) hdm)
    convert! H using 1
    ext q
    unfold rootCurveDerivative
    split_ifs with h₁ h₂
    · rfl
    · rfl
    · rw [heq q h₁ h₂]

theorem jointly_measurable_rootCurve_of_interior {X : Type*} [MeasurableSpace X]
    {l r : X → ℝ} {f df : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hlr : ∀ q, l q < r q)
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then f p.1 p.2 else 0))
    (hf : ∀ q y, y ∈ Icc (l q) (r q) →
      HasDerivWithinAt (f q) (df q y) (Icc (l q) (r q)) y) :
    Measurable (fun p : X × ℝ => rootCurveExtension (l p.1) (r p.1) (f p.1) (df p.1) p.2) ∧
      Measurable (fun p : X × ℝ => rootCurveDerivative (l p.1) (r p.1) (f p.1) (df p.1) p.2) := by
  exact measurable_rootCurve_of_interior (hl.comp measurable_fst) (hr.comp measurable_fst)
    measurable_snd (fun p => hlr p.1)
    (hm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    (fun p y hy => hf p.1 y hy)

theorem jointly_measurable_rootCurve_deriv {X : Type*} [MeasurableSpace X]
    {l r : X → ℝ} {f df : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hlr : ∀ q, l q < r q)
    (hfl : ∀ q, 0 < f q (l q)) (hfr : ∀ q, 0 < f q (r q))
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then f p.1 p.2 else 0))
    (hf : ∀ q y, y ∈ Icc (l q) (r q) →
      HasDerivWithinAt (f q) (df q y) (Icc (l q) (r q)) y) :
    Measurable (fun p : X × ℝ => deriv (rootCurveExtension (l p.1) (r p.1) (f p.1) (df p.1)) p.2) := by
  have H := (jointly_measurable_rootCurve_of_interior hl hr hlr hm hf).2
  convert! H using 1
  ext p
  exact (hasDerivAt_rootCurveExtension (hlr p.1) (hfl p.1) (hfr p.1) (hf p.1) p.2).deriv

end BianchiIX
