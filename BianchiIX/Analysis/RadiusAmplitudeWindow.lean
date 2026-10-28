import BianchiIX.Analysis.RadiusAmplitudeExtension

noncomputable section

namespace BianchiIX

open Set

def radiusAmplitudeWindowExtension (k U : ℝ → ℝ) (a b l r : ℝ) : ℝ → ℝ :=
  amplitudeCurveExtension l r (radiusAmplitude k U a b) (radiusAmplitudeSlope k U a b)

/-- A closed output window inherits continuous endpoint slopes and the original cone constant. -/
theorem radiusAmplitude_window_extension {k U W : ℝ → ℝ} {a b l r θ B : ℝ}
    (hab : a < b) (hlr : l < r) (hwindow : Icc l r ⊆ Icc (k b) (k a)) (hθ : θ ≤ 1)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hW : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 W x)
    (hposU : ∀ x ∈ Icc a b, 0 < U x) (hposW : ∀ x ∈ Icc a b, 0 < W x)
    (hconeU : ∀ x ∈ Icc a b, |deriv U x| ≤ θ * (Real.sqrt (U x) * |deriv k x|))
    (hconeW : ∀ x ∈ Icc a b, |deriv W x| ≤ θ * (Real.sqrt (W x) * |deriv k x|))
    (hB : ∀ x ∈ Icc a b, U x + W x ≤ B) :
    let u := radiusAmplitudeWindowExtension k U a b l r
    let w := radiusAmplitudeWindowExtension k W a b l r
    ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
      (∀ x ∈ Icc a b, k x ∈ Icc l r →
        u (k x) = U x ∧ w (k x) = W x ∧
        deriv u (k x) = deriv U x / deriv k x ∧ deriv w (k x) = deriv W x / deriv k x) ∧
      ∀ x : ℝ, 0 < u x ∧ 0 < w x ∧ u x + w x ≤ (25 / 16) * B ∧
        |deriv u x| ≤ θ * Real.sqrt (u x) ∧ |deriv w x| ≤ θ * Real.sqrt (w x) := by
  intro u w
  obtain ⟨_, _, hleft, hmaps, _, _⟩ := intervalRadiusInverse_control hab hk hd
  have Hdata (V : ℝ → ℝ) (hV : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 V x)
      (hpos : ∀ x ∈ Icc a b, 0 < V x)
      (hc : ∀ x ∈ Icc a b, |deriv V x| ≤ θ * (Real.sqrt (V x) * |deriv k x|)) :
      (∀ x ∈ Icc l r, 0 < radiusAmplitude k V a b x) ∧
      (∀ x ∈ Icc l r, HasDerivWithinAt (radiusAmplitude k V a b)
        (radiusAmplitudeSlope k V a b x) (Icc l r) x) ∧
      ContinuousOn (radiusAmplitudeSlope k V a b) (Icc l r) ∧
      ∀ x ∈ Icc l r, |radiusAmplitudeSlope k V a b x| ≤ θ * Real.sqrt (radiusAmplitude k V a b x) := by
    have hc1 (x : ℝ) (hx : x ∈ Icc a b) := (hc x hx).trans
      (mul_le_of_le_one_left (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hθ)
    obtain ⟨_, hp, hv, hdc, _⟩ := radiusAmplitude_data hab hk hd hV hpos hc1
    refine ⟨fun x hx => hp x (hwindow hx), fun x hx => (hv x (hwindow hx)).mono hwindow,
      hdc.mono hwindow, ?_⟩
    intro x hx
    let z := intervalRadiusInverse k a b x
    have hz : z ∈ Icc a b := hmaps (hwindow hx)
    change |deriv V z / deriv k z| ≤ θ * Real.sqrt (V z)
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr (hd z hz).ne)).mpr
    exact (hc z hz).trans_eq (by ring)
  obtain ⟨hpu, hdu, hcu, hconeU'⟩ := Hdata U hU hposU hconeU
  obtain ⟨hpw, hdw, hcw, hconeW'⟩ := Hdata W hW hposW hconeW
  refine ⟨contDiff_amplitudeCurveExtension hlr hpu hdu hcu,
    contDiff_amplitudeCurveExtension hlr hpw hdw hcw, ?_, ?_⟩
  · intro x hx hxJ
    have hmatch (V : ℝ → ℝ) (hpos : ∀ x ∈ Icc l r, 0 < radiusAmplitude k V a b x) :
        radiusAmplitudeWindowExtension k V a b l r (k x) = V x := by
      rw [radiusAmplitudeWindowExtension, amplitudeCurveExtension_middle hxJ (hpos _ hxJ).le,
        radiusAmplitude, hleft hx]
    refine ⟨hmatch U hpu, hmatch W hpw, ?_, ?_⟩
    · rw [show u = amplitudeCurveExtension l r (radiusAmplitude k U a b) (radiusAmplitudeSlope k U a b) by rfl,
        amplitudeCurveExtension_deriv_middle hlr hpu hdu hxJ, radiusAmplitudeSlope, hleft hx]
    · rw [show w = amplitudeCurveExtension l r (radiusAmplitude k W a b) (radiusAmplitudeSlope k W a b) by rfl,
        amplitudeCurveExtension_deriv_middle hlr hpw hdw hxJ, radiusAmplitudeSlope, hleft hx]
  · intro x
    exact ⟨amplitudeCurveExtension_pos hlr.le hpu hconeU' hθ x,
      amplitudeCurveExtension_pos hlr.le hpw hconeW' hθ x,
      amplitudeCurveExtension_pair_bound hlr.le hpu hpw hconeU' hconeW' hθ
        (fun y hy => hB _ (hmaps (hwindow hy))) x,
      amplitudeCurveExtension_cone hlr hpu hdu hconeU' hθ x,
      amplitudeCurveExtension_cone hlr hpw hdw hconeW' hθ x⟩

end BianchiIX
