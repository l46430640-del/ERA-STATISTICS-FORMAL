import BianchiIX.Analysis.RadiusAmplitudeExtension
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section

namespace BianchiIX

open Set Function

def closedIntervalFamily {X : Type*} (a b : X → ℝ) : Set (X × ℝ) :=
  {p | p.2 ∈ Icc (a p.1) (b p.1)}

theorem measurableSet_closedIntervalFamily {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    MeasurableSet (closedIntervalFamily a b) :=
  (measurableSet_le (ha.comp measurable_fst) measurable_snd).inter
    (measurableSet_le measurable_snd (hb.comp measurable_fst))

open scoped Classical in
/-- The same interval inverse is jointly measurable when both source endpoints vary measurably. -/
theorem jointly_measurable_variable_radiusAmplitude_interior {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hab : ∀ q, a q < b q) {k U : X → ℝ → ℝ}
    (hk : Measurable (fun p : closedIntervalFamily a b => k p.val.1 p.val.2))
    (hU : Measurable (fun p : closedIntervalFamily a b => U p.val.1 p.val.2))
    (hkc : ∀ q, ContinuousOn (k q) (Icc (a q) (b q)))
    (hanti : ∀ q, StrictAntiOn (k q) (Icc (a q) (b q))) :
    Measurable (fun p : X × ℝ => if k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1) then
      radiusAmplitude (k p.1) (U p.1) (a p.1) (b p.1) p.2 else 0) := by
  classical
  let D := closedIntervalFamily a b
  let : StandardBorelSpace D := (measurableSet_closedIntervalFamily ha hb).standardBorel
  let H : D → X × ℝ := fun p => (p.val.1, k p.val.1 p.val.2)
  have hmH : Measurable H := (measurable_fst.comp measurable_subtype_coe).prodMk hk
  have hiH : Injective H := by
    rintro ⟨⟨q, x⟩, hx⟩ ⟨⟨q', y⟩, hy⟩ h
    have hq : q = q' := congrArg Prod.fst h
    subst q'
    have hxy : x = y := (hanti q).injOn hx hy (congrArg Prod.snd h)
    exact Subtype.ext (Prod.ext rfl hxy)
  have he := hmH.measurableEmbedding hiH
  let V := Function.extend H (fun p : D => U p.val.1 p.val.2) (fun _ => (0 : ℝ))
  have hmV : Measurable V := he.measurable_extend hU measurable_const
  have hma' : Measurable (fun q => (⟨(q, a q), le_rfl, (hab q).le⟩ : D)) :=
    (measurable_id.prodMk ha).subtype_mk
  have hmb' : Measurable (fun q => (⟨(q, b q), (hab q).le, le_rfl⟩ : D)) :=
    (measurable_id.prodMk hb).subtype_mk
  have hma : Measurable (fun q => k q (a q)) := hk.comp hma'
  have hmb : Measurable (fun q => k q (b q)) := hk.comp hmb'
  have hS : MeasurableSet {p : X × ℝ | k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1)} :=
    (measurableSet_lt (hmb.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (hma.comp measurable_fst))
  have hmask : Measurable (fun p : X × ℝ =>
      if k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1) then V p else 0) :=
    Measurable.ite hS hmV measurable_const
  convert! hmask using 1
  ext p
  by_cases hp : k p.1 (b p.1) < p.2 ∧ p.2 < k p.1 (a p.1)
  · have himage := (hkc p.1).image_Icc_of_antitoneOn (hab p.1).le (hanti p.1).antitoneOn
    obtain ⟨x, hx, hval⟩ : p.2 ∈ k p.1 '' Icc (a p.1) (b p.1) := by
      rw [himage]
      exact ⟨hp.1.le, hp.2.le⟩
    have hinv := (hanti p.1).injOn.leftInvOn_invFunOn hx
    have hV : V p = U p.1 x := by
      have hHp : H (⟨(p.1, x), hx⟩ : D) = p := Prod.ext rfl hval
      rw [← hHp]
      exact hiH.extend_apply _ _ _
    simp [hV, radiusAmplitude, intervalRadiusInverse, ← hval, hinv]
  · simp [hp]

end BianchiIX
