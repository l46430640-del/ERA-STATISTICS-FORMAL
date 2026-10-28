import BianchiIX.Analysis.CurveMeasurability
import BianchiIX.Analysis.SmallParameters
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace BianchiIX

open Set

def amplitudeRootDerivative (U dU : ℝ → ℝ) (x : ℝ) : ℝ :=
  dU x / (2 * Real.sqrt (U x))

theorem hasDerivWithinAt_amplitudeRoot {U dU : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hpos : 0 < U x) (hU : HasDerivWithinAt U (dU x) s x) :
    HasDerivWithinAt (fun y => Real.sqrt (U y)) (amplitudeRootDerivative U dU x) s x :=
  hU.sqrt (ne_of_gt hpos)

theorem amplitudeRootDerivative_bound {U dU : ℝ → ℝ} {x θ : ℝ}
    (hpos : 0 < U x) (hcone : |dU x| ≤ θ * Real.sqrt (U x)) :
    |amplitudeRootDerivative U dU x| ≤ θ / 2 := by
  have hs : 0 < Real.sqrt (U x) := Real.sqrt_pos.mpr hpos
  rw [amplitudeRootDerivative, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt (U x))]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt (U x))).mpr
  nlinarith

theorem continuousOn_amplitudeRootDerivative {U dU : ℝ → ℝ} {s : Set ℝ}
    (hpos : ∀ x ∈ s, 0 < U x) (hU : ContinuousOn U s) (hdU : ContinuousOn dU s) :
    ContinuousOn (amplitudeRootDerivative U dU) s :=
  hdU.div (continuousOn_const.mul hU.sqrt)
    (fun x hx => ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.mpr (hpos x hx))))

def amplitudeCurveExtension (l r : ℝ) (U dU : ℝ → ℝ) (x : ℝ) : ℝ :=
  rootCurveExtension l r (fun y => Real.sqrt (U y)) (amplitudeRootDerivative U dU) x ^ 2

theorem amplitudeCurveExtension_middle {l r x : ℝ} {U dU : ℝ → ℝ}
    (hx : x ∈ Icc l r) (hpos : 0 ≤ U x) :
    amplitudeCurveExtension l r U dU x = U x := by
  rw [amplitudeCurveExtension, (rootCurveExtension_middle _ _ hx).1, Real.sq_sqrt hpos]

theorem hasDerivAt_amplitudeCurveExtension {l r : ℝ} (hlr : l < r) {U dU : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < U x)
    (hU : ∀ x ∈ Icc l r, HasDerivWithinAt U (dU x) (Icc l r) x) (x : ℝ) :
    HasDerivAt (amplitudeCurveExtension l r U dU)
      (2 * rootCurveExtension l r (fun y => Real.sqrt (U y)) (amplitudeRootDerivative U dU) x *
        rootCurveDerivative l r (fun y => Real.sqrt (U y)) (amplitudeRootDerivative U dU) x) x := by
  have H := hasDerivAt_rootCurveExtension (f := fun y => Real.sqrt (U y))
    (df := amplitudeRootDerivative U dU) hlr
    (Real.sqrt_pos.mpr (hpos l ⟨le_rfl, hlr.le⟩))
    (Real.sqrt_pos.mpr (hpos r ⟨hlr.le, le_rfl⟩))
    (fun y hy => hasDerivWithinAt_amplitudeRoot (hpos y hy) (hU y hy)) x
  convert! H.pow 2 using 1
  simp

theorem amplitudeCurveExtension_deriv_middle {l r x : ℝ} (hlr : l < r) {U dU : ℝ → ℝ}
    (hpos : ∀ y ∈ Icc l r, 0 < U y)
    (hU : ∀ y ∈ Icc l r, HasDerivWithinAt U (dU y) (Icc l r) y) (hx : x ∈ Icc l r) :
    deriv (amplitudeCurveExtension l r U dU) x = dU x := by
  rw [(hasDerivAt_amplitudeCurveExtension hlr hpos hU x).deriv,
    (rootCurveExtension_middle _ _ hx).1, (rootCurveExtension_middle _ _ hx).2]
  dsimp only [amplitudeRootDerivative]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (hpos x hx))]

theorem contDiff_amplitudeCurveExtension {l r : ℝ} (hlr : l < r) {U dU : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < U x)
    (hU : ∀ x ∈ Icc l r, HasDerivWithinAt U (dU x) (Icc l r) x)
    (hdU : ContinuousOn dU (Icc l r)) : ContDiff ℝ 1 (amplitudeCurveExtension l r U dU) := by
  exact (contDiff_rootCurveExtension (f := fun y => Real.sqrt (U y))
    (df := amplitudeRootDerivative U dU) hlr
    (Real.sqrt_pos.mpr (hpos l ⟨le_rfl, hlr.le⟩))
    (Real.sqrt_pos.mpr (hpos r ⟨hlr.le, le_rfl⟩))
    (fun x hx => hasDerivWithinAt_amplitudeRoot (hpos x hx) (hU x hx))
    (continuousOn_amplitudeRootDerivative hpos (fun x hx => (hU x hx).continuousWithinAt) hdU)).pow 2

theorem amplitudeCurveExtension_pos {l r θ : ℝ} (hlr : l ≤ r) {U dU : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < U x)
    (hcone : ∀ x ∈ Icc l r, |dU x| ≤ θ * Real.sqrt (U x)) (hθ : θ ≤ 1) (x : ℝ) :
    0 < amplitudeCurveExtension l r U dU x :=
  pow_pos (rootCurveExtension_pos hlr (fun y hy => Real.sqrt_pos.mpr (hpos y hy))
    (fun y hy => amplitudeRootDerivative_bound (hpos y hy) (hcone y hy)) hθ x) 2

theorem amplitudeCurveExtension_cone {l r θ : ℝ} (hlr : l < r) {U dU : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < U x)
    (hU : ∀ x ∈ Icc l r, HasDerivWithinAt U (dU x) (Icc l r) x)
    (hcone : ∀ x ∈ Icc l r, |dU x| ≤ θ * Real.sqrt (U x)) (hθ : θ ≤ 1) (x : ℝ) :
    |deriv (amplitudeCurveExtension l r U dU) x| ≤
      θ * Real.sqrt (amplitudeCurveExtension l r U dU x) :=
  rootCurveExtension_square_cone hlr (fun y hy => Real.sqrt_pos.mpr (hpos y hy))
    (fun y hy => amplitudeRootDerivative_bound (hpos y hy) (hcone y hy)) hθ
    (fun y hy => hasDerivWithinAt_amplitudeRoot (hpos y hy) (hU y hy)) x

theorem amplitudeCurveExtension_pair_bound_sharp {l r θ B : ℝ} (hlr : l ≤ r)
    {U W dU dW : ℝ → ℝ}
    (hU : ∀ x ∈ Icc l r, 0 < U x) (hW : ∀ x ∈ Icc l r, 0 < W x)
    (hdU : ∀ x ∈ Icc l r, |dU x| ≤ θ * Real.sqrt (U x))
    (hdW : ∀ x ∈ Icc l r, |dW x| ≤ θ * Real.sqrt (W x))
    (hθ : θ ≤ 1) (hB : ∀ x ∈ Icc l r, U x + W x ≤ B) (x : ℝ) :
    amplitudeCurveExtension l r U dU x + amplitudeCurveExtension l r W dW x ≤
      (1 + θ / 4) ^ 2 * B := by
  apply rootCurveExtension_pair_bound_sharp hlr
    (fun y hy => Real.sqrt_pos.mpr (hU y hy)) (fun y hy => Real.sqrt_pos.mpr (hW y hy))
    (fun y hy => amplitudeRootDerivative_bound (hU y hy) (hdU y hy))
    (fun y hy => amplitudeRootDerivative_bound (hW y hy) (hdW y hy)) hθ
  intro y hy
  simpa only [Real.sq_sqrt (hU y hy).le, Real.sq_sqrt (hW y hy).le] using hB y hy

theorem amplitudeCurveExtension_pair_bound {l r θ B : ℝ} (hlr : l ≤ r)
    {U W dU dW : ℝ → ℝ}
    (hU : ∀ x ∈ Icc l r, 0 < U x) (hW : ∀ x ∈ Icc l r, 0 < W x)
    (hdU : ∀ x ∈ Icc l r, |dU x| ≤ θ * Real.sqrt (U x))
    (hdW : ∀ x ∈ Icc l r, |dW x| ≤ θ * Real.sqrt (W x))
    (hθ : θ ≤ 1) (hB : ∀ x ∈ Icc l r, U x + W x ≤ B) (x : ℝ) :
    amplitudeCurveExtension l r U dU x + amplitudeCurveExtension l r W dW x ≤
      (25 / 16) * B := by
  apply rootCurveExtension_pair_bound hlr
    (fun y hy => Real.sqrt_pos.mpr (hU y hy)) (fun y hy => Real.sqrt_pos.mpr (hW y hy))
    (fun y hy => amplitudeRootDerivative_bound (hU y hy) (hdU y hy))
    (fun y hy => amplitudeRootDerivative_bound (hW y hy) (hdW y hy)) hθ
  intro y hy
  simpa only [Real.sq_sqrt (hU y hy).le, Real.sq_sqrt (hW y hy).le] using hB y hy

theorem amplitudeCurveExtension_pair_contraction {l r θ B Bmax C : ℝ} (hlr : l ≤ r)
    {U W dU dW : ℝ → ℝ}
    (hU : ∀ x ∈ Icc l r, 0 < U x) (hW : ∀ x ∈ Icc l r, 0 < W x)
    (hdU : ∀ x ∈ Icc l r, |dU x| ≤ θ * Real.sqrt (U x))
    (hdW : ∀ x ∈ Icc l r, |dW x| ≤ θ * Real.sqrt (W x))
    (hθ : θ ≤ 1) (hB : 0 < B) (hmax : B ≤ Bmax) (hC : 0 ≤ C)
    (hbudget : (25 / 16 : ℝ) * C * Bmax ^ (17 / 30 : ℝ) ≤ 1)
    (hsmall : ∀ x ∈ Icc l r, U x + W x ≤ C * B ^ (19 / 10 : ℝ)) (x : ℝ) :
    amplitudeCurveExtension l r U dU x + amplitudeCurveExtension l r W dW x ≤ B ^ (4 / 3 : ℝ) :=
  (amplitudeCurveExtension_pair_bound hlr hU hW hdU hdW hθ hsmall x).trans
    (extension_amplitude_gain hB hmax hC hbudget)

theorem jointly_measurable_amplitudeCurve {X : Type*} [MeasurableSpace X]
    {l r : X → ℝ} {U dU : X → ℝ → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hlr : ∀ q, l q < r q)
    (hpos : ∀ q x, x ∈ Icc (l q) (r q) → 0 < U q x)
    (hm : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then U p.1 p.2 else 0))
    (hU : ∀ q x, x ∈ Icc (l q) (r q) →
      HasDerivWithinAt (U q) (dU q x) (Icc (l q) (r q)) x) :
    Measurable (fun p : X × ℝ => amplitudeCurveExtension (l p.1) (r p.1) (U p.1) (dU p.1) p.2) ∧
      Measurable (fun p : X × ℝ => deriv (amplitudeCurveExtension (l p.1) (r p.1) (U p.1) (dU p.1)) p.2) := by
  have hmroot : Measurable (fun p : X × ℝ =>
      if l p.1 < p.2 ∧ p.2 < r p.1 then Real.sqrt (U p.1 p.2) else 0) := by
    convert! Real.continuous_sqrt.measurable.comp hm using 1
    ext p
    by_cases hp : l p.1 < p.2 ∧ p.2 < r p.1 <;> simp [hp]
  obtain ⟨hs, hds⟩ := jointly_measurable_rootCurve_of_interior hl hr hlr hmroot
    (fun q x hx => hasDerivWithinAt_amplitudeRoot (hpos q x hx) (hU q x hx))
  refine ⟨hs.pow_const 2, ?_⟩
  have H := (hs.const_mul 2).mul hds
  convert! H using 1
  ext p
  exact (hasDerivAt_amplitudeCurveExtension (hlr p.1) (hpos p.1) (hU p.1) p.2).deriv

end BianchiIX
