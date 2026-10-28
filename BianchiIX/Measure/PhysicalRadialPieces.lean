import BianchiIX.Measure.OriginalRadialCoordinates

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def shearRadialInterval (a d ε n₂ n₃ : ℝ) : Set ℝ :=
  Ioo a (2 * a) ∩ {r | max n₂ n₃ ≤ ε * r ∧ r < d}

def angularRadialInterval (otherWall : Bool) (a d θ ζ : ℝ) : Set ℝ :=
  Ioo a (2 * a) ∩ {r | (if otherWall then ζ < r else ζ ≤ r) ∧ r < d ∧ |θ| * r < d}

theorem shearRadialInterval_eq {a d ε n₂ n₃ : ℝ} (hε : 0 < ε) :
    shearRadialInterval a d ε n₂ n₃ = Ioo a (2 * a) ∩ Ico (max n₂ n₃ / ε) d := by
  ext r
  simp only [shearRadialInterval, mem_inter_iff, mem_Ico, mem_ofPred_eq]
  rw [div_le_iff₀ hε, mul_comm r ε]

theorem angularRadialInterval_eq {a d θ ζ : ℝ} (hθ : θ ≠ 0) :
    angularRadialInterval false a d θ ζ =
      Ioo a (2 * a) ∩ Ico ζ (min d (d / |θ|)) := by
  ext r
  simp only [angularRadialInterval, Bool.false_eq_true, ↓reduceIte, mem_inter_iff,
    mem_ofPred_eq, mem_Ico, lt_min_iff]
  rw [lt_div_iff₀ (abs_pos.mpr hθ), mul_comm r |θ|]

theorem angularRadialInterval_other_eq {a d θ ζ : ℝ} (hθ : θ ≠ 0) :
    angularRadialInterval true a d θ ζ =
      Ioo a (2 * a) ∩ Ioo ζ (min d (d / |θ|)) := by
  ext r
  simp only [angularRadialInterval, ↓reduceIte, mem_inter_iff,
    mem_ofPred_eq, mem_Ioo, lt_min_iff]
  rw [lt_div_iff₀ (abs_pos.mpr hθ), mul_comm r |θ|]

/-- The zero-shear fiber has no artificial division-by-zero cutoff. -/
theorem angularRadialInterval_zero {a d ζ : ℝ} (hd : 0 < d) :
    angularRadialInterval false a d 0 ζ = Ioo a (2 * a) ∩ Ico ζ d ∧
    angularRadialInterval true a d 0 ζ = Ioo a (2 * a) ∩ Ioo ζ d := by
  constructor <;> ext r <;> simp [angularRadialInterval, hd]

def shearRadialDomain (a d ε : ℝ) : Set SectionCoordinates :=
  {z | 0 < z 1 ∧ 0 < z 2 ∧ z 0 ∈ shearRadialInterval a d ε (z 1) (z 2)}

def angularRadialDomain (otherWall : Bool) (a d L : ℝ) : Set SectionCoordinates :=
  {z | |z 1| < L ∧ 0 < z 2 ∧ z 0 ∈ angularRadialInterval otherWall a d (z 1) (z 2)}

theorem measurableSet_shearRadialDomain (a d ε : ℝ) : MeasurableSet (shearRadialDomain a d ε) := by
  have h₁ : MeasurableSet {z : SectionCoordinates | 0 < z 1} := measurableSet_lt (by fun_prop) (by fun_prop)
  have h₂ : MeasurableSet {z : SectionCoordinates | 0 < z 2} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hr : MeasurableSet {z : SectionCoordinates | z 0 ∈ Ioo a (2 * a)} :=
    measurableSet_Ioo.preimage (by fun_prop)
  have hm : MeasurableSet {z : SectionCoordinates | max (z 1) (z 2) ≤ ε * z 0} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hd : MeasurableSet {z : SectionCoordinates | z 0 < d} := measurableSet_lt (by fun_prop) (by fun_prop)
  exact h₁.inter (h₂.inter (hr.inter (hm.inter hd)))

theorem measurableSet_angularRadialDomain (otherWall : Bool) (a d L : ℝ) :
    MeasurableSet (angularRadialDomain otherWall a d L) := by
  have horder : MeasurableSet {z : SectionCoordinates | if otherWall then z 2 < z 0 else z 2 ≤ z 0} := by
    cases otherWall
    · exact measurableSet_le (by fun_prop) (by fun_prop)
    · exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hθ : MeasurableSet {z : SectionCoordinates | |z 1| < L} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hζ : MeasurableSet {z : SectionCoordinates | 0 < z 2} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hr : MeasurableSet {z : SectionCoordinates | z 0 ∈ Ioo a (2 * a)} :=
    measurableSet_Ioo.preimage (by fun_prop)
  have hd : MeasurableSet {z : SectionCoordinates | z 0 < d} := measurableSet_lt (by fun_prop) (by fun_prop)
  have hs : MeasurableSet {z : SectionCoordinates | |z 1| * z 0 < d} :=
    measurableSet_lt (by fun_prop) (by fun_prop)
  exact hθ.inter (hζ.inter (hr.inter (horder.inter (hd.inter hs))))

theorem signedShearLogCoordinates_radialDomain_subset_chart {h a d ε σ : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hdh : d ≤ h / 8)
    (hε : ε ≤ 1) (hσ : |σ| = 1) :
    signedShearLogCoordinates σ '' shearRadialDomain a d ε ⊆ mainWallChartDomain h := by
  rintro _ ⟨z, hz, rfl⟩
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have hm : max (z 1) (z 2) ≤ z 0 := hz.2.2.2.1.trans (by nlinarith)
  apply mainWallChartDomain_of_small hh hh1 hdh
  · simpa [signedShearLogCoordinates, abs_mul, hσ, abs_of_pos hr] using hz.2.2.2.2.le
  · simpa [signedShearLogCoordinates, Real.exp_log hz.1] using (le_max_left (z 1) (z 2)).trans (hm.trans hz.2.2.2.2.le)
  · simpa [signedShearLogCoordinates, Real.exp_log hz.2.1] using (le_max_right (z 1) (z 2)).trans (hm.trans hz.2.2.2.2.le)

theorem scaledAngularLogCoordinates_radialDomain_subset_chart {h a d L : ℝ}
    (otherWall : Bool) (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hdh : d ≤ h / 8) :
    scaledAngularLogCoordinates (1 / 2) '' angularRadialDomain otherWall a d L ⊆ mainWallChartDomain h := by
  rintro _ ⟨z, hz, rfl⟩
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have hζ : z 2 ≤ z 0 := by
    have ho := hz.2.2.2.1
    cases otherWall
    · exact ho
    · exact le_of_lt ho
  apply mainWallChartDomain_of_small hh hh1 hdh
  · simpa [scaledAngularLogCoordinates, abs_mul, abs_of_pos hr] using hz.2.2.2.2.2.le
  · simpa [scaledAngularLogCoordinates, Real.exp_log hr] using hz.2.2.2.2.1.le
  · simpa [scaledAngularLogCoordinates, Real.exp_log hz.2.1] using hζ.trans hz.2.2.2.2.1.le

theorem measurableSet_shearRadialPiece {a d ε σ : ℝ} {F : Set SectionCoordinates}
    (hσ : σ ≠ 0) (hF : MeasurableSet F) :
    MeasurableSet (signedShearLogCoordinates σ '' (shearRadialDomain a d ε ∩ F)) := by
  have hpos : ∀ z ∈ shearRadialDomain a d ε ∩ F, 0 < z 1 ∧ 0 < z 2 :=
    fun _ hz => ⟨hz.1.1, hz.1.2.1⟩
  exact ((measurableSet_shearRadialDomain a d ε).inter hF).image_of_continuousOn_injOn
    (fun z hz => (hasFDerivAt_signedShearLogCoordinates (hpos z hz).1
      (hpos z hz).2).continuousAt.continuousWithinAt)
    ((signedShearLogCoordinates_injOn hσ).mono hpos)

theorem measurableSet_angularRadialPiece {a d L : ℝ} {F : Set SectionCoordinates}
    (otherWall : Bool) (ha : 0 < a) (hF : MeasurableSet F) :
    MeasurableSet (orderedAngularLogCoordinates otherWall '' (angularRadialDomain otherWall a d L ∩ F)) := by
  have hpos : ∀ z ∈ angularRadialDomain otherWall a d L ∩ F, 0 < z 0 ∧ 0 < z 2 :=
    fun _ hz => ⟨ha.trans hz.1.2.2.1.1, hz.1.2.1⟩
  have hbase : MeasurableSet (scaledAngularLogCoordinates (1 / 2) ''
      (angularRadialDomain otherWall a d L ∩ F)) :=
    ((measurableSet_angularRadialDomain otherWall a d L).inter hF).image_of_continuousOn_injOn
      (fun z hz => (hasFDerivAt_scaledAngularLogCoordinates (by norm_num) (hpos z hz).1
        (hpos z hz).2).continuousAt.continuousWithinAt)
      ((scaledAngularLogCoordinates_injOn (by norm_num : (0 : ℝ) < 1 / 2)).mono hpos)
  cases otherWall
  · exact hbase
  · change MeasurableSet ((mainWallReflection ∘ scaledAngularLogCoordinates (1 / 2)) '' _)
    rw [image_comp]
    exact measurableSet_mainWallReflection_image hbase

theorem angularRadialPieces_disjoint {a b d e L M : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Disjoint (orderedAngularLogCoordinates false '' angularRadialDomain false a d L)
      (orderedAngularLogCoordinates true '' angularRadialDomain true b e M) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hx0 : 0 < x 0 := ha.trans hx.2.2.1.1
  have hy0 : 0 < y 0 := hb.trans hy.2.2.1.1
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  simp only [orderedAngularLogCoordinates, Bool.false_eq_true, ↓reduceIte,
    mainWallReflection, scaledAngularLogCoordinates, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_zero] at h1 h2
  norm_num at h1 h2
  have h10 : y 2 = x 0 := Real.log_injOn_pos hy.2.1 hx0 h1
  have h20 : y 0 = x 2 := Real.log_injOn_pos hy0 hx.2.1 h2
  have hxy : x 2 ≤ x 0 := hx.2.2.2.1
  have hyx : y 2 < y 0 := hy.2.2.2.1
  linarith

theorem signedShearRadialPieces_disjoint {a b d e ε δ : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Disjoint (signedShearLogCoordinates 1 '' shearRadialDomain a d ε)
      (signedShearLogCoordinates (-1) '' shearRadialDomain b e δ) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hx0 : 0 < x 0 := ha.trans hx.2.2.1.1
  have hy0 : 0 < y 0 := hb.trans hy.2.2.1.1
  have h0 : (-1 : ℝ) * y 0 = 1 * x 0 := congrFun heq 0
  linarith

/-- Exact integration of a joint Borel failure predicate over the physical shear piece. -/
theorem mainWallOriginalMeasure_shearRadialPiece {h a d ε σ : ℝ} {F : Set SectionCoordinates}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hdh : d ≤ h / 8)
    (hε : ε ≤ 1) (hσ : |σ| = 1) (hF : MeasurableSet F) :
    mainWallOriginalMeasure h (signedShearLogCoordinates σ '' (shearRadialDomain a d ε ∩ F)) =
      ∫⁻ n₂ : ℝ, ∫⁻ n₃ : ℝ, ENNReal.ofReal (1 / (n₂ * n₃)) *
        ∫⁻ r in {r : ℝ | 0 < n₂ ∧ 0 < n₃ ∧
          r ∈ shearRadialInterval a d ε n₂ n₃ ∧ ![r, n₂, n₃] ∈ F},
          ENNReal.ofReal (mainWallOriginalDensity h (signedShearLogCoordinates σ ![r, n₂, n₃])) := by
  have hA := (measurableSet_shearRadialDomain a d ε).inter hF
  rw [mainWallOriginalMeasure_signedShearLogCoordinates hσ hA
    (fun z hz => ⟨hz.1.1, hz.1.2.1⟩)
    ((image_mono inter_subset_left).trans
      (signedShearLogCoordinates_radialDomain_subset_chart hh hh1 ha hdh hε hσ))]
  have hf : Measurable (fun z : SectionCoordinates => ENNReal.ofReal (1 / (z 1 * z 2)) *
      ENNReal.ofReal (mainWallOriginalDensity h (signedShearLogCoordinates σ z))) := by
    have hw : Measurable (fun z : SectionCoordinates => ENNReal.ofReal (1 / (z 1 * z 2))) := by fun_prop
    exact hw.mul (((measurable_mainWallOriginalDensity h).comp
      (by unfold signedShearLogCoordinates; fun_prop)).ennreal_ofReal)
  rw [setLIntegral_three_coordinates hA hf]
  apply lintegral_congr
  intro n₂
  apply lintegral_congr
  intro n₃
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  congr 1
  ext r
  simp [shearRadialDomain, and_assoc]

/-- Both angular orders use the actual radius window, with equality of walls assigned once. -/
theorem mainWallOriginalMeasure_angularRadialPiece {h a d L : ℝ} {F : Set SectionCoordinates}
    (otherWall : Bool) (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hdh : d ≤ h / 8)
    (hF : MeasurableSet F) :
    mainWallOriginalMeasure h
        (orderedAngularLogCoordinates otherWall '' (angularRadialDomain otherWall a d L ∩ F)) =
      ∫⁻ θ : ℝ, ∫⁻ ζ : ℝ, ENNReal.ofReal (1 / ζ) *
        ∫⁻ r in {r : ℝ | |θ| < L ∧ 0 < ζ ∧
          r ∈ angularRadialInterval otherWall a d θ ζ ∧ ![r, θ, ζ] ∈ F},
          ENNReal.ofReal (mainWallOriginalDensity h (orderedAngularLogCoordinates otherWall ![r, θ, ζ])) := by
  have hA := (measurableSet_angularRadialDomain otherWall a d L).inter hF
  rw [mainWallOriginalMeasure_orderedAngularLogCoordinates otherWall hA
    (fun z hz => ⟨ha.trans hz.1.2.2.1.1, hz.1.2.1⟩)
    ((image_mono inter_subset_left).trans
      (scaledAngularLogCoordinates_radialDomain_subset_chart otherWall hh hh1 ha hdh))]
  have hf : Measurable (fun z : SectionCoordinates => ENNReal.ofReal (1 / z 2) *
      ENNReal.ofReal (mainWallOriginalDensity h (orderedAngularLogCoordinates otherWall z))) := by
    have hw : Measurable (fun z : SectionCoordinates => ENNReal.ofReal (1 / z 2)) := by fun_prop
    have hc : Measurable (orderedAngularLogCoordinates otherWall) := by
      unfold orderedAngularLogCoordinates scaledAngularLogCoordinates mainWallReflection
      cases otherWall with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; fun_prop
      | true => simp only [↓reduceIte]; fun_prop
    exact hw.mul (((measurable_mainWallOriginalDensity h).comp hc).ennreal_ofReal)
  rw [setLIntegral_three_coordinates hA hf]
  apply lintegral_congr
  intro θ
  apply lintegral_congr
  intro ζ
  simp only [Matrix.cons_val_two]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  congr 1
  ext r
  simp [angularRadialDomain, and_assoc]

end BianchiIX
