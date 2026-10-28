import BianchiIX.Analysis.RootCurveExtension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- A budget at the largest amplitude remains valid at every smaller scale. -/
theorem rpow_gain_bound {B Bmax C p q : ℝ} (hB : 0 < B) (hmax : B ≤ Bmax)
    (hC : 0 ≤ C) (hpq : q ≤ p) (hbudget : C * Bmax ^ (p - q) ≤ 1) :
    C * B ^ p ≤ B ^ q := by
  have hs : C * B ^ (p - q) ≤ 1 :=
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hB.le hmax (sub_nonneg.mpr hpq)) hC).trans hbudget
  calc
    C * B ^ p = (C * B ^ (p - q)) * B ^ q := by
      rw [mul_assoc, ← Real.rpow_add hB, sub_add_cancel]
    _ ≤ 1 * B ^ q := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hB.le _)
    _ = B ^ q := one_mul _

theorem extension_amplitude_gain {B Bmax C : ℝ} (hB : 0 < B) (hmax : B ≤ Bmax)
    (hC : 0 ≤ C) (hbudget : (25 / 16 : ℝ) * C * Bmax ^ (17 / 30 : ℝ) ≤ 1) :
    (25 / 16 : ℝ) * (C * B ^ (19 / 10 : ℝ)) ≤ B ^ (4 / 3 : ℝ) := by
  have H := rpow_gain_bound (C := (25 / 16 : ℝ) * C)
    (p := 19 / 10) (q := 4 / 3) hB hmax (by positivity) (by norm_num)
    (by norm_num; exact hbudget)
  simpa only [mul_assoc] using H

theorem rootCurveExtension_pair_contraction {l r θ B Bmax C : ℝ} (hlr : l ≤ r)
    {f g df dg : ℝ → ℝ}
    (hf : ∀ x ∈ Icc l r, 0 < f x) (hg : ∀ x ∈ Icc l r, 0 < g x)
    (hdf : ∀ x ∈ Icc l r, |df x| ≤ θ / 2) (hdg : ∀ x ∈ Icc l r, |dg x| ≤ θ / 2)
    (hθ : θ ≤ 1) (hB : 0 < B) (hmax : B ≤ Bmax) (hC : 0 ≤ C)
    (hbudget : (25 / 16 : ℝ) * C * Bmax ^ (17 / 30 : ℝ) ≤ 1)
    (hsmall : ∀ x ∈ Icc l r, f x ^ 2 + g x ^ 2 ≤ C * B ^ (19 / 10 : ℝ)) (x : ℝ) :
    rootCurveExtension l r f df x ^ 2 + rootCurveExtension l r g dg x ^ 2 ≤ B ^ (4 / 3 : ℝ) :=
  (rootCurveExtension_pair_bound hlr hf hg hdf hdg hθ hsmall x).trans
    (extension_amplitude_gain hB hmax hC hbudget)

/-- Finitely many positive-power errors admit one common amplitude threshold. -/
theorem exists_common_rpow_budget {ι : Type*} (s : Finset ι) {C p ε : ι → ℝ} {upper : ℝ}
    (hC : ∀ i ∈ s, 0 ≤ C i) (hp : ∀ i ∈ s, 0 < p i)
    (hε : ∀ i ∈ s, 0 < ε i) (hu : 0 < upper) :
    ∃ Bmax : ℝ, 0 < Bmax ∧ Bmax < upper ∧
      ∀ B ∈ Ioc 0 Bmax, ∀ i ∈ s, C i * B ^ p i < ε i := by
  have he : ∀ᶠ B : ℝ in 𝓝 0, ∀ i ∈ s, C i * B ^ p i < ε i := by
    apply (s.eventually_all).mpr
    intro i hi
    have H : Tendsto (fun B : ℝ => C i * B ^ p i) (𝓝 0) (𝓝 0) := by
      simpa only [Real.zero_rpow (ne_of_gt (hp i hi)), mul_zero] using
        ((Real.continuousAt_rpow_const 0 (p i) (Or.inr (hp i hi).le)).tendsto.const_mul (C i))
    exact H.eventually (gt_mem_nhds (hε i hi))
  have hpos : ∀ᶠ B : ℝ in 𝓝[>] 0, 0 < B := self_mem_nhdsWithin
  have hupper : ∀ᶠ B : ℝ in 𝓝[>] 0, B < upper :=
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hu)
  have hsmall := he.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
  obtain ⟨Bmax, hpos, hupper, hbudget⟩ := (hpos.and (hupper.and hsmall)).exists
  refine ⟨Bmax, hpos, hupper, fun B hB i hi => ?_⟩
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hB.1.le hB.2 (hp i hi).le)
    (hC i hi)).trans_lt (hbudget i hi)

theorem eta_parameter_bounds {η N₀ N₁ : ℝ} (hN₀ : 0 ≤ N₀) (hN₁ : 0 ≤ N₁)
    (hη : η ≤ 1 / (64 * (1 + N₀ + N₁))) :
    η < 1 / 16 ∧ η * N₀ < 1 / 2 ∧ η * N₁ < 1 / 2 := by
  have hd : 0 < 64 * (1 + N₀ + N₁) := by positivity
  have hbudget := (le_div_iff₀ hd).mp hη
  by_cases hη0 : 0 ≤ η
  · have h₀ := mul_nonneg hη0 hN₀
    have h₁ := mul_nonneg hη0 hN₁
    constructor
    · nlinarith
    constructor <;> nlinarith
  · have hηn : η ≤ 0 := le_of_not_ge hη0
    exact ⟨by linarith, (mul_nonpos_of_nonpos_of_nonneg hηn hN₀).trans_lt (by norm_num),
      (mul_nonpos_of_nonpos_of_nonneg hηn hN₁).trans_lt (by norm_num)⟩

end BianchiIX
