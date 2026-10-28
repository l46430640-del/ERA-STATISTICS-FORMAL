import BianchiIX.Measure.ClippedLogIntegral
import Mathlib.Analysis.Convex.Function

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem concaveOn_unitIntegral {s : Set ℝ} {f : ℝ → ℝ → ℝ} (hs : Convex ℝ s)
    (hi : ∀ ell ∈ s, IntervalIntegrable (f ell) volume 0 1)
    (hc : ∀ x ∈ Ioo (0 : ℝ) 1, ConcaveOn ℝ s (fun ell => f ell x)) :
    ConcaveOn ℝ s (fun ell => ∫ x in (0 : ℝ)..1, f ell x) := by
  refine ⟨hs, ?_⟩
  intro ell₁ h₁ ell₂ h₂ a b ha hb hab
  have hsum := hs h₁ h₂ ha hb hab
  have H := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
    (((hi ell₁ h₁).const_mul a).add ((hi ell₂ h₂).const_mul b)) (hi _ hsum)
    (fun x hx => by simpa only [smul_eq_mul] using (hc x hx).2 h₁ h₂ ha hb hab)
  simpa only [intervalIntegral.integral_add ((hi ell₁ h₁).const_mul a) ((hi ell₂ h₂).const_mul b),
    intervalIntegral.integral_const_mul, smul_eq_mul] using H

theorem integral_clippedPowerDensity_mono {ell₁ ell₂ B₁ B₂ δ : ℝ}
    (hl : 0 ≤ ell₁) (hB : 0 ≤ B₁) (hδ : 0 < δ) (hle : ell₁ ≤ ell₂) (hBe : B₁ ≤ B₂) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensity ell₁ B₁ δ x) ≤
      ∫ x in (0 : ℝ)..1, clippedPowerDensity ell₂ B₂ δ x := by
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
    (intervalIntegrable_clippedPowerDensity hl hB hδ (by norm_num))
    (intervalIntegrable_clippedPowerDensity (hl.trans hle) (hB.trans hBe) hδ (by norm_num))
  intro x hx
  exact div_le_div_of_nonneg_right
    (min_le_min hle (mul_le_mul_of_nonneg_right hBe (Real.rpow_nonneg hx.1.le δ))) hx.1.le

theorem integral_clippedPowerDensityTwo_mono {ell₁ ell₂ B₁ B₂ δ : ℝ}
    (hl : 0 < ell₁) (hB : 0 < B₁) (hδ : 0 < δ) (hle : ell₁ ≤ ell₂) (hBe : B₁ ≤ B₂) :
    (∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell₁ B₁ δ x) ≤
      ∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell₂ B₂ δ x := by
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
    (integral_clippedPowerDensityTwo hl hB hδ).1
    (integral_clippedPowerDensityTwo (hl.trans_le hle) (hB.trans_le hBe) hδ).1
  intro x hx
  exact div_le_div_of_nonneg_right (integral_clippedPowerDensity_mono hl.le
    (mul_nonneg hB.le (Real.rpow_nonneg hx.1.le δ)) hδ hle
    (mul_le_mul_of_nonneg_right hBe (Real.rpow_nonneg hx.1.le δ))) hx.1.le

theorem concaveOn_integral_clippedPowerDensity {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) :
    ConcaveOn ℝ (Ioi 0) (fun ell => ∫ x in (0 : ℝ)..1, clippedPowerDensity ell B δ x) := by
  apply concaveOn_unitIntegral (convex_Ioi 0)
    (fun ell hell => intervalIntegrable_clippedPowerDensity hell.le hB hδ (by norm_num))
  intro x hx
  have H : ConcaveOn ℝ (Ioi 0) (fun ell : ℝ => min ell (B * x ^ δ)) :=
    (concaveOn_id (convex_Ioi 0)).inf (concaveOn_const _ (convex_Ioi 0))
  simpa only [clippedPowerDensity, div_eq_mul_inv, smul_eq_mul, mul_comm] using
    ConcaveOn.smul (inv_nonneg.mpr hx.1.le) H

theorem concaveOn_integral_clippedPowerDensityTwo {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) :
    ConcaveOn ℝ (Ioi 0) (fun ell => ∫ x in (0 : ℝ)..1, clippedPowerDensityTwo ell B δ x) := by
  apply concaveOn_unitIntegral (convex_Ioi 0)
    (fun ell hell => (integral_clippedPowerDensityTwo hell hB hδ).1)
  intro x hx
  have H := concaveOn_integral_clippedPowerDensity (mul_nonneg hB.le (Real.rpow_nonneg hx.1.le δ)) hδ
  simpa only [clippedPowerDensityTwo, div_eq_mul_inv, smul_eq_mul, mul_comm] using
    ConcaveOn.smul (inv_nonneg.mpr hx.1.le) H

end BianchiIX
