import BianchiIX.Analysis.RadiusAmplitudeWindow
import BianchiIX.Analysis.VariableRadiusAmplitudeMeasurability

noncomputable section

namespace BianchiIX

open Set

set_option maxHeartbeats 600000 in
/-- A measurable choice of closed output windows preserves joint measurability of values and slopes. -/
theorem jointly_measurable_radiusAmplitudeWindowExtension {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ q, a q < b q) {k U : X → ℝ → ℝ} {l r : X → ℝ}
    (hl : Measurable l) (hr : Measurable r) (hlr : ∀ q, l q < r q)
    (hwindow : ∀ q, Icc (l q) (r q) ⊆ Icc (k q (b q)) (k q (a q)))
    (hkm : Measurable (fun p : closedIntervalFamily a b => k p.val.1 p.val.2))
    (hUm : Measurable (fun p : closedIntervalFamily a b => U p.val.1 p.val.2))
    (hk : ∀ q x, x ∈ Icc (a q) (b q) → ContDiffAt ℝ 1 (k q) x)
    (hd : ∀ q x, x ∈ Icc (a q) (b q) → deriv (k q) x < 0)
    (hU : ∀ q x, x ∈ Icc (a q) (b q) → ContDiffAt ℝ 1 (U q) x)
    (hpos : ∀ q x, x ∈ Icc (a q) (b q) → 0 < U q x) :
    Measurable (fun p : X × ℝ =>
      radiusAmplitudeWindowExtension (k p.1) (U p.1) (a p.1) (b p.1) (l p.1) (r p.1) p.2) ∧
    Measurable (fun p : X × ℝ =>
      deriv (radiusAmplitudeWindowExtension (k p.1) (U p.1) (a p.1) (b p.1) (l p.1) (r p.1)) p.2) := by
  classical
  have hi (q : X) := intervalRadiusInverse_control (hab q) (hk q) (hd q)
  have hcont (q : X) : ContinuousOn (k q) (Icc (a q) (b q)) :=
    fun x hx => (hk q x hx).continuousAt.continuousWithinAt
  have hanti (q : X) : StrictAntiOn (k q) (Icc (a q) (b q)) :=
    strictAntiOn_of_deriv_neg (convex_Icc (a q) (b q)) (hcont q)
      (fun x hx => hd q x (interior_subset hx))
  have hm := jointly_measurable_variable_radiusAmplitude_interior ha hb hab hkm hUm hcont hanti
  have hS : MeasurableSet {p : X × ℝ | l p.1 < p.2 ∧ p.2 < r p.1} :=
    (measurableSet_lt (hl.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (hr.comp measurable_fst))
  have hmwin : Measurable (fun p : X × ℝ => if l p.1 < p.2 ∧ p.2 < r p.1 then
      radiusAmplitude (k p.1) (U p.1) (a p.1) (b p.1) p.2 else 0) := by
    have H : Measurable (fun p : X × ℝ => if l p.1 < p.2 ∧ p.2 < r p.1 then
        (if k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1) then
          radiusAmplitude (k p.1) (U p.1) (a p.1) (b p.1) p.2 else 0) else 0) :=
      Measurable.ite hS hm measurable_const
    convert! H using 1
    ext p
    by_cases hp : l p.1 < p.2 ∧ p.2 < r p.1
    · have hleft := (hwindow p.1 ⟨le_rfl, (hlr p.1).le⟩).1
      have hright := (hwindow p.1 ⟨(hlr p.1).le, le_rfl⟩).2
      simp [hp, hleft.trans_lt hp.1, hp.2.trans_le hright]
    · simp [hp]
  have hrootpos (q : X) (x : ℝ) (hx : x ∈ Icc (l q) (r q)) :
      0 < radiusAmplitude (k q) (U q) (a q) (b q) x :=
    hpos q _ ((hi q).2.2.2.1 (hwindow q hx))
  have hrootder (q : X) (x : ℝ) (hx : x ∈ Icc (l q) (r q)) :
      HasDerivWithinAt (radiusAmplitude (k q) (U q) (a q) (b q))
        (radiusAmplitudeSlope (k q) (U q) (a q) (b q) x) (Icc (l q) (r q)) x := by
    have hx' := hwindow q hx
    have H := ((hU q _ ((hi q).2.2.2.1 hx')).differentiableAt
      (by norm_num)).hasDerivAt.comp_hasDerivWithinAt x
      (((hi q).2.2.2.2.2 x hx').mono (hwindow q))
    simpa only [radiusAmplitude, radiusAmplitudeSlope, Function.comp_def, div_eq_mul_inv] using! H
  exact jointly_measurable_amplitudeCurve
    (U := fun q => radiusAmplitude (k q) (U q) (a q) (b q))
    (dU := fun q => radiusAmplitudeSlope (k q) (U q) (a q) (b q))
    hl hr hlr hrootpos hmwin hrootder

end BianchiIX
