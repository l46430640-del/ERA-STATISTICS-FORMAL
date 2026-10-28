import BianchiIX.Measure.PhysicalRadialPieces
import BianchiIX.Measure.DyadicCover

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def mainWallOpenSection (d : ℝ) : Set SectionCoordinates :=
  {z | |z 0| < d ∧ max (Real.exp (-z 1)) (Real.exp (-z 2)) < d}

def mainWallRadialRadius (ε : ℝ) (z : SectionCoordinates) : ℝ :=
  if max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ ε * |z 0| then |z 0|
    else max (Real.exp (-z 1)) (Real.exp (-z 2))

/-- The two summands distinguish shear signs and angular wall orders. -/
abbrev RadialPieceIndex := (Bool ⊕ Bool) × ℕ

def radialPieceMap (k : Bool ⊕ Bool) : SectionCoordinates → SectionCoordinates :=
  match k with
  | Sum.inl neg => signedShearLogCoordinates (if neg then -1 else 1)
  | Sum.inr other => orderedAngularLogCoordinates other

def radialPieceDomain (d ε : ℝ) (i : RadialPieceIndex) : Set SectionCoordinates :=
  match i.1 with
  | Sum.inl _ => shearRadialDomain (dyadicScale d i.2) d ε
  | Sum.inr other => angularRadialDomain other (dyadicScale d i.2) d (1 / ε)

def physicalRadialPiece (d ε : ℝ) (i : RadialPieceIndex) : Set SectionCoordinates :=
  radialPieceMap i.1 '' radialPieceDomain d ε i

def radialPieceInverse (k : Bool ⊕ Bool) (z : SectionCoordinates) : SectionCoordinates :=
  match k with
  | Sum.inl neg => ![(if neg then -1 else 1) * z 0, Real.exp (-z 1), Real.exp (-z 2)]
  | Sum.inr false => ![Real.exp (-z 1), z 0 / Real.exp (-z 1), Real.exp (-z 2)]
  | Sum.inr true => ![Real.exp (-z 2), -z 0 / Real.exp (-z 2), Real.exp (-z 1)]

theorem measurable_radialPieceInverse (k : Bool ⊕ Bool) : Measurable (radialPieceInverse k) := by
  rcases k with neg | other <;> cases ‹Bool› <;> unfold radialPieceInverse <;> fun_prop

theorem radialPieceInverse_map {d ε : ℝ} (hd : 0 < d) {i : RadialPieceIndex}
    {z : SectionCoordinates} (hz : z ∈ radialPieceDomain d ε i) :
    radialPieceInverse i.1 (radialPieceMap i.1 z) = z := by
  rcases i with ⟨neg | other, j⟩
  · have h₁ : 0 < z 1 := hz.1
    have h₂ : 0 < z 2 := hz.2.1
    cases neg <;> ext n <;> fin_cases n <;>
      simp [radialPieceInverse, radialPieceMap, signedShearLogCoordinates, Real.exp_log h₁, Real.exp_log h₂]
  · have hr : 0 < z 0 := (dyadicScale_pos hd j).trans hz.2.2.1.1
    have hζ : 0 < z 2 := hz.2.1
    cases other <;> ext n <;> fin_cases n <;>
      simp [radialPieceInverse, radialPieceMap, orderedAngularLogCoordinates,
        scaledAngularLogCoordinates, mainWallReflection, Real.exp_log hr, Real.exp_log hζ, hr.ne']

theorem measurableSet_mainWallOpenSection (d : ℝ) : MeasurableSet (mainWallOpenSection d) := by
  have hs : MeasurableSet {z : SectionCoordinates | |z 0| < d} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hm : MeasurableSet {z : SectionCoordinates | max (Real.exp (-z 1)) (Real.exp (-z 2)) < d} :=
    measurableSet_lt (by fun_prop) measurable_const
  exact hs.inter hm

theorem measurable_mainWallRadialRadius (ε : ℝ) : Measurable (mainWallRadialRadius ε) := by
  have hS : MeasurableSet {z : SectionCoordinates |
      max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ ε * |z 0|} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  exact Measurable.ite hS (by fun_prop) (by fun_prop)

theorem mainWallRadialRadius_pos {ε : ℝ} (hε : 0 < ε) (z : SectionCoordinates) :
    0 < mainWallRadialRadius ε z := by
  have hm : 0 < max (Real.exp (-z 1)) (Real.exp (-z 2)) :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  unfold mainWallRadialRadius
  split_ifs with hs
  · exact (mul_pos_iff_of_pos_left hε).mp (hm.trans_le hs)
  · exact hm

theorem mainWallRadialRadius_lt {d ε : ℝ} {z : SectionCoordinates}
    (hz : z ∈ mainWallOpenSection d) : mainWallRadialRadius ε z < d := by
  unfold mainWallRadialRadius
  split_ifs
  · exact hz.1
  · exact hz.2

theorem signedShearLogCoordinates_radial_data {a d ε σ : ℝ} {z : SectionCoordinates}
    (ha : 0 < a) (hσ : |σ| = 1) (hz : z ∈ shearRadialDomain a d ε) :
    |signedShearLogCoordinates σ z 0| = z 0 ∧
    max (Real.exp (-(signedShearLogCoordinates σ z) 1))
      (Real.exp (-(signedShearLogCoordinates σ z) 2)) = max (z 1) (z 2) := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  simp [signedShearLogCoordinates, abs_mul, hσ, abs_of_pos hr,
    Real.exp_log hz.1, Real.exp_log hz.2.1]

theorem orderedAngularLogCoordinates_radial_data {a d L : ℝ} {z : SectionCoordinates}
    (other : Bool) (ha : 0 < a) (hz : z ∈ angularRadialDomain other a d L) :
    |orderedAngularLogCoordinates other z 0| = |z 1| * z 0 ∧
    max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
      (Real.exp (-(orderedAngularLogCoordinates other z) 2)) = z 0 := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have ho := hz.2.2.2.1
  cases other with
  | false =>
    simp [orderedAngularLogCoordinates, scaledAngularLogCoordinates, abs_mul, abs_of_pos hr,
      Real.exp_log hr, Real.exp_log hz.2.1, max_eq_left ho]
  | true =>
    simp [orderedAngularLogCoordinates, mainWallReflection, scaledAngularLogCoordinates,
      abs_mul, abs_of_pos hr, Real.exp_log hr, Real.exp_log hz.2.1,
      max_eq_right (le_of_lt ho)]

theorem shearRadialPiece_region {a d ε σ : ℝ} {y : SectionCoordinates}
    (ha : 0 < a) (hσ : |σ| = 1) (hy : y ∈ signedShearLogCoordinates σ '' shearRadialDomain a d ε) :
    max (Real.exp (-y 1)) (Real.exp (-y 2)) ≤ ε * |y 0| ∧
      mainWallRadialRadius ε y ∈ Ioo a (2 * a) := by
  rcases hy with ⟨z, hz, rfl⟩
  obtain ⟨hs, hm⟩ := signedShearLogCoordinates_radial_data ha hσ hz
  have hreg : max (Real.exp (-(signedShearLogCoordinates σ z) 1))
      (Real.exp (-(signedShearLogCoordinates σ z) 2)) ≤ ε * |signedShearLogCoordinates σ z 0| := by
    rw [hs, hm]
    exact hz.2.2.2.1
  refine ⟨hreg, ?_⟩
  unfold mainWallRadialRadius
  rw [if_pos hreg, hs]
  exact hz.2.2.1

theorem angularRadialPiece_region {a d ε : ℝ} {y : SectionCoordinates}
    (other : Bool) (ha : 0 < a) (hε : 0 < ε)
    (hy : y ∈ orderedAngularLogCoordinates other '' angularRadialDomain other a d (1 / ε)) :
    ε * |y 0| < max (Real.exp (-y 1)) (Real.exp (-y 2)) ∧
      mainWallRadialRadius ε y ∈ Ioo a (2 * a) := by
  rcases hy with ⟨z, hz, rfl⟩
  obtain ⟨hs, hm⟩ := orderedAngularLogCoordinates_radial_data other ha hz
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have hθ : ε * |z 1| < 1 := by
    have H := (lt_div_iff₀ hε).mp hz.1
    nlinarith
  have hreg : ε * |orderedAngularLogCoordinates other z 0| <
      max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
        (Real.exp (-(orderedAngularLogCoordinates other z) 2)) := by
    rw [hs, hm]
    nlinarith [mul_lt_mul_of_pos_right hθ hr]
  refine ⟨hreg, ?_⟩
  unfold mainWallRadialRadius
  rw [if_neg (not_le.mpr hreg), hm]
  exact hz.2.2.1

theorem physicalRadialPiece_radius {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {i : RadialPieceIndex} {z : SectionCoordinates} (hz : z ∈ physicalRadialPiece d ε i) :
    mainWallRadialRadius ε z ∈ Ioo (dyadicScale d i.2) (2 * dyadicScale d i.2) := by
  rcases i with ⟨neg | other, j⟩
  · exact (shearRadialPiece_region (dyadicScale_pos hd j)
      (by cases neg <;> norm_num) hz).2
  · exact (angularRadialPiece_region other (dyadicScale_pos hd j) hε hz).2

theorem physicalRadialPiece_subset_openSection {d ε : ℝ} (hd : 0 < d) (hε : ε ≤ 1)
    (i : RadialPieceIndex) : physicalRadialPiece d ε i ⊆ mainWallOpenSection d := by
  rcases i with ⟨neg | other, j⟩
  · rintro _ ⟨z, hz, rfl⟩
    have ha := dyadicScale_pos hd j
    obtain ⟨hs, hm⟩ := signedShearLogCoordinates_radial_data ha
      (show |(if neg then -1 else 1 : ℝ)| = 1 by cases neg <;> norm_num) hz
    change |signedShearLogCoordinates _ z 0| < d ∧
      max (Real.exp (-(signedShearLogCoordinates _ z) 1))
        (Real.exp (-(signedShearLogCoordinates _ z) 2)) < d
    rw [hs, hm]
    refine ⟨hz.2.2.2.2, (hz.2.2.2.1.trans ?_).trans_lt hz.2.2.2.2⟩
    have hr : 0 < z 0 := ha.trans hz.2.2.1.1
    nlinarith
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hs, hm⟩ := orderedAngularLogCoordinates_radial_data other (dyadicScale_pos hd j) hz
    change |orderedAngularLogCoordinates other z 0| < d ∧
      max (Real.exp (-(orderedAngularLogCoordinates other z) 1))
        (Real.exp (-(orderedAngularLogCoordinates other z) 2)) < d
    rw [hs, hm]
    exact ⟨hz.2.2.2.2.2, hz.2.2.2.2.1⟩

theorem shear_angular_radialPieces_disjoint {a b d e ε : ℝ} {σ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (hσ : |σ| = 1) (other : Bool) :
    Disjoint (signedShearLogCoordinates σ '' shearRadialDomain a d ε)
      (orderedAngularLogCoordinates other '' angularRadialDomain other b e (1 / ε)) := by
  apply Set.disjoint_left.mpr
  intro z hs ha'
  exact (not_lt_of_ge (shearRadialPiece_region ha hσ hs).1)
    (angularRadialPiece_region other hb hε ha').1

theorem physicalRadialPieces_pairwiseDisjoint {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    Pairwise (fun i j : RadialPieceIndex => Disjoint (physicalRadialPiece d ε i) (physicalRadialPiece d ε j)) := by
  rintro ⟨k, n⟩ ⟨l, m⟩ hij
  by_cases hnm : n = m
  · subst m
    have hkl : k ≠ l := by intro h; exact hij (by cases h; rfl)
    rcases k with neg | other <;> rcases l with neg' | other'
    · cases neg <;> cases neg'
      · exact False.elim (hkl rfl)
      · exact signedShearRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
      · exact (signedShearRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)).symm
      · exact False.elim (hkl rfl)
    · exact shear_angular_radialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
        hε (by cases neg <;> norm_num) other'
    · exact (shear_angular_radialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
        hε (by cases neg' <;> norm_num) other).symm
    · cases other <;> cases other'
      · exact False.elim (hkl rfl)
      · exact angularRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)
      · exact (angularRadialPieces_disjoint (dyadicScale_pos hd n) (dyadicScale_pos hd n)).symm
      · exact False.elim (hkl rfl)
  · apply Set.disjoint_left.mpr
    intro z hz hw
    exact Set.disjoint_left.mp (pairwise_disjoint_dyadicScale_Ioc hd.le hnm)
      ⟨(physicalRadialPiece_radius hd hε hz).1, (physicalRadialPiece_radius hd hε hz).2.le⟩
      ⟨(physicalRadialPiece_radius hd hε hw).1, (physicalRadialPiece_radius hd hε hw).2.le⟩

theorem exists_mem_physicalRadialPiece {d ε : ℝ} {z : SectionCoordinates} {j : ℕ}
    (hε : 0 < ε) (hz : z ∈ mainWallOpenSection d)
    (hr : mainWallRadialRadius ε z ∈ Ioo (dyadicScale d j) (2 * dyadicScale d j)) :
    ∃ k : Bool ⊕ Bool, z ∈ physicalRadialPiece d ε (k, j) := by
  by_cases hs : max (Real.exp (-z 1)) (Real.exp (-z 2)) ≤ ε * |z 0|
  · rw [mainWallRadialRadius, if_pos hs] at hr
    have hD : ![|z 0|, Real.exp (-z 1), Real.exp (-z 2)] ∈
        shearRadialDomain (dyadicScale d j) d ε :=
      ⟨Real.exp_pos _, Real.exp_pos _, hr, hs, hz.1⟩
    by_cases hs0 : 0 ≤ z 0
    · refine ⟨Sum.inl false, ![|z 0|, Real.exp (-z 1), Real.exp (-z 2)], hD, ?_⟩
      ext i
      fin_cases i <;> simp [radialPieceMap, signedShearLogCoordinates, abs_of_nonneg hs0]
    · refine ⟨Sum.inl true, ![|z 0|, Real.exp (-z 1), Real.exp (-z 2)], hD, ?_⟩
      ext i
      fin_cases i <;> simp [radialPieceMap, signedShearLogCoordinates, abs_of_neg (lt_of_not_ge hs0)]
  · rw [mainWallRadialRadius, if_neg hs] at hr
    have hgap := lt_of_not_ge hs
    by_cases hc : Real.exp (-z 2) ≤ Real.exp (-z 1)
    · rw [max_eq_left hc] at hr hgap
      have hθ : |z 0 / Real.exp (-z 1)| < 1 / ε := by
        rw [abs_div, abs_of_pos (Real.exp_pos _)]
        apply (div_lt_div_iff₀ (Real.exp_pos _) hε).mpr
        nlinarith
      have hprod : |z 0 / Real.exp (-z 1)| * Real.exp (-z 1) = |z 0| := by
        rw [abs_div, abs_of_pos (Real.exp_pos _), div_mul_cancel₀ _ (Real.exp_ne_zero _)]
      have hD : ![Real.exp (-z 1), z 0 / Real.exp (-z 1), Real.exp (-z 2)] ∈
          angularRadialDomain false (dyadicScale d j) d (1 / ε) := by
        refine ⟨hθ, Real.exp_pos _, hr, hc, ?_, ?_⟩
        · exact (le_max_left _ _).trans_lt hz.2
        · change |z 0 / Real.exp (-z 1)| * Real.exp (-z 1) < d
          rw [hprod]
          exact hz.1
      refine ⟨Sum.inr false, ![Real.exp (-z 1), z 0 / Real.exp (-z 1), Real.exp (-z 2)], hD, ?_⟩
      ext i
      fin_cases i <;> simp [radialPieceMap, orderedAngularLogCoordinates,
        scaledAngularLogCoordinates, Real.exp_ne_zero]
    · have hclt := lt_of_not_ge hc
      rw [max_eq_right hclt.le] at hr hgap
      have hθ : |-z 0 / Real.exp (-z 2)| < 1 / ε := by
        rw [abs_div, abs_neg, abs_of_pos (Real.exp_pos _)]
        apply (div_lt_div_iff₀ (Real.exp_pos _) hε).mpr
        nlinarith
      have hprod : |-z 0 / Real.exp (-z 2)| * Real.exp (-z 2) = |z 0| := by
        rw [abs_div, abs_neg, abs_of_pos (Real.exp_pos _), div_mul_cancel₀ _ (Real.exp_ne_zero _)]
      have hD : ![Real.exp (-z 2), -z 0 / Real.exp (-z 2), Real.exp (-z 1)] ∈
          angularRadialDomain true (dyadicScale d j) d (1 / ε) := by
        refine ⟨hθ, Real.exp_pos _, hr, hclt, ?_, ?_⟩
        · exact (le_max_right _ _).trans_lt hz.2
        · change |-z 0 / Real.exp (-z 2)| * Real.exp (-z 2) < d
          rw [hprod]
          exact hz.1
      refine ⟨Sum.inr true, ![Real.exp (-z 2), -z 0 / Real.exp (-z 2), Real.exp (-z 1)], hD, ?_⟩
      ext i
      fin_cases i <;> simp [radialPieceMap, orderedAngularLogCoordinates,
        scaledAngularLogCoordinates, mainWallReflection, Real.exp_ne_zero]

end BianchiIX
