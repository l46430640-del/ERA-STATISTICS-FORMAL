import BianchiIX.Analysis.VariableRadiusAmplitudeMeasurability

noncomputable section

namespace BianchiIX

open Set Function

open scoped Classical in
/-- A family measurable on a measurable label set remains measurable after extension by zero. -/
theorem jointly_measurable_zero_extension {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {S : Set X} (hS : MeasurableSet S) {F : X → Y → ℝ}
    (hF : Measurable (fun p : S × Y => F p.1.val p.2)) :
    Measurable (fun p : X × Y => if p.1 ∈ S then F p.1 p.2 else 0) := by
  classical
  let D : Set (X × Y) := {p | p.1 ∈ S}
  have hD : MeasurableSet D := hS.preimage measurable_fst
  have hm : Measurable (fun p : D => ((⟨p.val.1, p.property⟩ : S), p.val.2)) :=
    (measurable_fst.comp measurable_subtype_coe).subtype_mk.prodMk
      (measurable_snd.comp measurable_subtype_coe)
  simpa only [D, mem_ofPred_eq, Function.comp_def, dite_eq_ite] using
    (hF.comp hm).dite (g := fun _ => (0 : ℝ)) measurable_const hD

/-- The interior radius graph is jointly measurable, using the same closed-interval inverse. -/
theorem jointly_measurable_radiusAmplitude_interior {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : ℝ} (hab : a < b) {k U : X → ℝ → ℝ}
    (hk : Measurable (fun p : X × Icc a b => k p.1 p.2))
    (hU : Measurable (fun p : X × Icc a b => U p.1 p.2))
    (hkc : ∀ q, ContinuousOn (k q) (Icc a b))
    (hanti : ∀ q, StrictAntiOn (k q) (Icc a b)) :
    Measurable (fun p : X × ℝ => if k p.1 b < p.2 ∧ p.2 < k p.1 a then
      radiusAmplitude (k p.1) (U p.1) a b p.2 else 0) := by
  let T : closedIntervalFamily (fun _ : X => a) (fun _ => b) → X × Icc a b :=
    fun p => (p.val.1, ⟨p.val.2, p.property⟩)
  have hT : Measurable T := (measurable_fst.comp measurable_subtype_coe).prodMk
    (measurable_snd.comp measurable_subtype_coe).subtype_mk
  exact jointly_measurable_variable_radiusAmplitude_interior measurable_const measurable_const
    (fun _ => hab) (hk.comp hT) (hU.comp hT) hkc hanti

set_option maxHeartbeats 600000 in
/-- Radius reparametrization and root-amplitude extension preserve joint measurability in the labels. -/
theorem jointly_measurable_radiusAmplitudeExtension {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : ℝ} (hab : a < b) {k U : X → ℝ → ℝ}
    (hkm : Measurable (fun p : X × Icc a b => k p.1 p.2))
    (hUm : Measurable (fun p : X × Icc a b => U p.1 p.2))
    (hk : ∀ q x, x ∈ Icc a b → ContDiffAt ℝ 1 (k q) x)
    (hd : ∀ q x, x ∈ Icc a b → deriv (k q) x < 0)
    (hU : ∀ q x, x ∈ Icc a b → ContDiffAt ℝ 1 (U q) x)
    (hpos : ∀ q x, x ∈ Icc a b → 0 < U q x) :
    Measurable (fun p : X × ℝ => radiusAmplitudeExtension (k p.1) (U p.1) a b p.2) ∧
      Measurable (fun p : X × ℝ => deriv (radiusAmplitudeExtension (k p.1) (U p.1) a b) p.2) := by
  have hi (q : X) := intervalRadiusInverse_control hab (hk q) (hd q)
  have hma : Measurable (fun q => k q a) := hkm.comp
    (measurable_id.prodMk (measurable_const (a := (⟨a, le_rfl, hab.le⟩ : Icc a b))))
  have hmb : Measurable (fun q => k q b) := hkm.comp
    (measurable_id.prodMk (measurable_const (a := (⟨b, hab.le, le_rfl⟩ : Icc a b))))
  have hcont (q : X) : ContinuousOn (k q) (Icc a b) :=
    fun x hx => (hk q x hx).continuousAt.continuousWithinAt
  have hanti (q : X) : StrictAntiOn (k q) (Icc a b) :=
    strictAntiOn_of_deriv_neg (convex_Icc a b) (hcont q) (fun x hx => hd q x (interior_subset hx))
  have hm := jointly_measurable_radiusAmplitude_interior hab hkm hUm hcont hanti
  have hrootpos (q : X) (x : ℝ) (hx : x ∈ Icc (k q b) (k q a)) :
      0 < radiusAmplitude (k q) (U q) a b x := hpos q _ ((hi q).2.2.2.1 hx)
  have hrootder (q : X) (x : ℝ) (hx : x ∈ Icc (k q b) (k q a)) :
      HasDerivWithinAt (radiusAmplitude (k q) (U q) a b)
        (radiusAmplitudeSlope (k q) (U q) a b x) (Icc (k q b) (k q a)) x := by
    have H := ((hU q _ ((hi q).2.2.2.1 hx)).differentiableAt (by norm_num)).hasDerivAt.comp_hasDerivWithinAt x
      ((hi q).2.2.2.2.2 x hx)
    simpa only [radiusAmplitude, radiusAmplitudeSlope, Function.comp_def, div_eq_mul_inv] using! H
  exact jointly_measurable_amplitudeCurve
    (U := fun q => radiusAmplitude (k q) (U q) a b)
    (dU := fun q => radiusAmplitudeSlope (k q) (U q) a b)
    hmb hma (fun q => (hi q).1) hrootpos hm hrootder

end BianchiIX
