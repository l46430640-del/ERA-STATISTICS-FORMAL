import BianchiIX.Analysis.IntervalRadiusInverse
import BianchiIX.Analysis.AmplitudeExtension

noncomputable section

namespace BianchiIX

open Set

def radiusAmplitude (k U : ℝ → ℝ) (a b x : ℝ) : ℝ := U (intervalRadiusInverse k a b x)

def radiusAmplitudeSlope (k U : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  deriv U (intervalRadiusInverse k a b x) / deriv k (intervalRadiusInverse k a b x)

def radiusAmplitudeExtension (k U : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  amplitudeCurveExtension (k b) (k a) (radiusAmplitude k U a b) (radiusAmplitudeSlope k U a b)

/-- Radius reparametrization preserves the square-root cone, with continuous endpoint slopes. -/
theorem radiusAmplitude_data {k U : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hpos : ∀ x ∈ Icc a b, 0 < U x)
    (hcone : ∀ x ∈ Icc a b, |deriv U x| ≤ Real.sqrt (U x) * |deriv k x|) :
    let J := Icc (k b) (k a)
    let u := radiusAmplitude k U a b
    let du := radiusAmplitudeSlope k U a b
    (∀ x ∈ Icc a b, u (k x) = U x) ∧ (∀ x ∈ J, 0 < u x) ∧
      (∀ x ∈ J, HasDerivWithinAt u (du x) J x) ∧ ContinuousOn du J ∧
      ∀ x ∈ J, |du x| ≤ Real.sqrt (u x) := by
  intro J u du
  obtain ⟨_, _, hleft, hmaps, _, hder⟩ := intervalRadiusInverse_control hab hk hd
  let g := intervalRadiusInverse k a b
  have hgc : ContinuousOn g J := fun x hx => (hder x hx).continuousWithinAt
  have hdk : ContinuousOn (deriv k) (Icc a b) := fun x hx =>
    ((hk x hx).derivWithin (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousAt.continuousWithinAt
  have hdU : ContinuousOn (deriv U) (Icc a b) := fun x hx =>
    ((hU x hx).derivWithin (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousAt.continuousWithinAt
  refine ⟨?_, (fun x hx => hpos (g x) (hmaps hx)), ?_, ?_, ?_⟩
  · intro x hx
    exact congrArg U (hleft hx)
  · intro x hx
    simpa only [u, du, J, g, radiusAmplitude, radiusAmplitudeSlope, Function.comp_def, div_eq_mul_inv] using!
      (((hU (g x) (hmaps hx)).differentiableAt (by norm_num)).hasDerivAt.comp_hasDerivWithinAt x (hder x hx))
  · exact (hdU.comp hgc hmaps).div (hdk.comp hgc hmaps) (fun x hx => (hd (g x) (hmaps hx)).ne)
  · intro x hx
    change |deriv U (g x) / deriv k (g x)| ≤ Real.sqrt (U (g x))
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr (hd (g x) (hmaps hx)).ne)).mpr (hcone (g x) (hmaps hx))

/-- A physical radial curve has a canonical global C1 amplitude extension in the radius coordinate. -/
theorem radiusAmplitudeExtension_pair {k U W : ℝ → ℝ} {a b B : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x) (hd : ∀ x ∈ Icc a b, deriv k x < 0)
    (hU : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 U x) (hW : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 W x)
    (hposU : ∀ x ∈ Icc a b, 0 < U x) (hposW : ∀ x ∈ Icc a b, 0 < W x)
    (hconeU : ∀ x ∈ Icc a b, |deriv U x| ≤ Real.sqrt (U x) * |deriv k x|)
    (hconeW : ∀ x ∈ Icc a b, |deriv W x| ≤ Real.sqrt (W x) * |deriv k x|)
    (hB : ∀ x ∈ Icc a b, U x + W x ≤ B) :
    let u := radiusAmplitudeExtension k U a b
    let w := radiusAmplitudeExtension k W a b
    ContDiff ℝ 1 u ∧ ContDiff ℝ 1 w ∧
      (∀ x ∈ Icc a b, u (k x) = U x ∧ w (k x) = W x ∧
        deriv u (k x) = deriv U x / deriv k x ∧ deriv w (k x) = deriv W x / deriv k x) ∧
      ∀ x : ℝ, 0 < u x ∧ 0 < w x ∧ u x + w x ≤ (25 / 16) * B ∧
        |deriv u x| ≤ Real.sqrt (u x) ∧ |deriv w x| ≤ Real.sqrt (w x) := by
  intro u w
  obtain ⟨hba, himage, hleft, hmaps, _, _⟩ := intervalRadiusInverse_control hab hk hd
  obtain ⟨hmatchU, hpu, hdu, hcu, hconeU'⟩ := radiusAmplitude_data hab hk hd hU hposU hconeU
  obtain ⟨hmatchW, hpw, hdw, hcw, hconeW'⟩ := radiusAmplitude_data hab hk hd hW hposW hconeW
  have hconeU1 (x : ℝ) (hx : x ∈ Icc (k b) (k a)) :
      |radiusAmplitudeSlope k U a b x| ≤ 1 * Real.sqrt (radiusAmplitude k U a b x) := by
    simpa only [one_mul] using hconeU' x hx
  have hconeW1 (x : ℝ) (hx : x ∈ Icc (k b) (k a)) :
      |radiusAmplitudeSlope k W a b x| ≤ 1 * Real.sqrt (radiusAmplitude k W a b x) := by
    simpa only [one_mul] using hconeW' x hx
  have hsum (x : ℝ) (hx : x ∈ Icc (k b) (k a)) :
      radiusAmplitude k U a b x + radiusAmplitude k W a b x ≤ B := hB _ (hmaps hx)
  refine ⟨contDiff_amplitudeCurveExtension hba hpu hdu hcu,
    contDiff_amplitudeCurveExtension hba hpw hdw hcw, ?_, ?_⟩
  · intro x hx
    have hxJ : k x ∈ Icc (k b) (k a) := by rw [← himage]; exact mem_image_of_mem k hx
    refine ⟨(amplitudeCurveExtension_middle hxJ (hpu _ hxJ).le).trans (hmatchU x hx),
      (amplitudeCurveExtension_middle hxJ (hpw _ hxJ).le).trans (hmatchW x hx), ?_, ?_⟩
    · change deriv (amplitudeCurveExtension _ _ _ _) (k x) = _
      rw [amplitudeCurveExtension_deriv_middle hba hpu hdu hxJ]
      change deriv U (intervalRadiusInverse k a b (k x)) / deriv k (intervalRadiusInverse k a b (k x)) = _
      rw [hleft hx]
    · change deriv (amplitudeCurveExtension _ _ _ _) (k x) = _
      rw [amplitudeCurveExtension_deriv_middle hba hpw hdw hxJ]
      change deriv W (intervalRadiusInverse k a b (k x)) / deriv k (intervalRadiusInverse k a b (k x)) = _
      rw [hleft hx]
  · intro x
    refine ⟨amplitudeCurveExtension_pos hba.le hpu hconeU1 le_rfl x,
      amplitudeCurveExtension_pos hba.le hpw hconeW1 le_rfl x,
      amplitudeCurveExtension_pair_bound hba.le hpu hpw hconeU1 hconeW1 le_rfl hsum x, ?_, ?_⟩
    · simpa only [u, radiusAmplitudeExtension, one_mul] using amplitudeCurveExtension_cone hba hpu hdu hconeU1 le_rfl x
    · simpa only [w, radiusAmplitudeExtension, one_mul] using amplitudeCurveExtension_cone hba hpw hdw hconeW1 le_rfl x

end BianchiIX
