import BianchiIX.Measure.RestartRadialPartition
import BianchiIX.Measure.AngularRestartChoice
import BianchiIX.Measure.ShearRegionStatistics
import BianchiIX.Statistics.EraTypicalCapRestriction

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem shearUnselectedSection_reflection (a ε P : ℝ) (z : SectionCoordinates) :
    mainWallReflection z ∈ shearUnselectedSection a ε P ↔ z ∈ shearUnselectedSection a ε P := by
  simp [shearUnselectedSection, shearSectionLayer, mainWallReflection, and_left_comm, and_comm, and_assoc]

theorem angularUnselectedSection_reflection (a L P : ℝ) (z : SectionCoordinates) :
    mainWallReflection z ∈ angularUnselectedSection a L P ↔ z ∈ angularUnselectedSection a L P := by
  change (max (Real.exp (-z 2)) (Real.exp (-z 1)) ∈ Icc a (2 * a) ∧
    |-z 0| ≤ L * max (Real.exp (-z 2)) (Real.exp (-z 1)) ∧
    a ^ P < min (Real.exp (-z 2)) (Real.exp (-z 1))) ↔ _
  rw [max_comm (Real.exp (-z 2)) (Real.exp (-z 1)),
    min_comm (Real.exp (-z 2)) (Real.exp (-z 1)), abs_neg]
  rfl

theorem shearRadialDomain_swap {a d ε : ℝ} {z : SectionCoordinates}
    (hz : z ∈ shearRadialDomain a d ε) : ![z 0, z 2, z 1] ∈ shearRadialDomain a d ε := by
  refine ⟨hz.2.1, hz.1, hz.2.2.1, ?_, hz.2.2.2.2⟩
  change max (z 2) (z 1) ≤ ε * z 0
  simpa only [max_comm] using hz.2.2.2.1

/-- A positive shear failure belongs to the already estimated selected or unselected layer. -/
theorem shearRadialFailure_subset_layer {h s a d ε P η σ Bcap Bother : ℝ} {J : ℕ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 128) (hP : 4 ≤ P)
    (hcap : Bcap ≤ 1) (hsmall : 800 * a ≤ Bcap) {z : SectionCoordinates}
    (hz : z ∈ shearRadialDomain a d ε)
    (hf : z ∈ labelRadialFailure a (restartShearCommonLabelSet ε a P)
      (EraSurvivor.typicalDomain η J σ Bcap)
      (fun l r => (restartShearAmplitudeBudget a l.1 l.2, restartShearReturnState h s l.1 l.2 r))) :
    signedShearLogCoordinates 1 z ∈
      mainWallSymmetrization (restartShearCommonFailureSection h s a ε P η J σ Bother) ∪
        shearUnselectedSection a ε P := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have hn : max (z 1) (z 2) ≤ 2 * ε * a :=
    hz.2.2.2.1.trans ((mul_le_mul_of_nonneg_left hz.2.2.1.2.le hε.1).trans_eq (by ring))
  have h₂ : 0 < z 1 ∧ z 1 ≤ 2 * ε * a := ⟨hz.1, (le_max_left _ _).trans hn⟩
  have h₃ : 0 < z 2 ∧ z 2 ≤ 2 * ε * a := ⟨hz.2.1, (le_max_right _ _).trans hn⟩
  by_cases hl : (z 1, z 2) ∈ restartShearCommonLabelSet ε a P
  · have hεa : 2 * ε * a ≤ a := by nlinarith only [ha, hε.2]
    have hb := (restartShearAmplitudeBudget_le_of_min ⟨ha, ha1⟩ hP
      ⟨h₂.1, h₂.2.trans hεa⟩ ⟨h₃.1, h₃.2.trans hεa⟩ hl.2.2).2.trans hsmall
    have hbad : z 0 ∈ restartShearFailureFibers h s a η J σ Bother (z 1, z 2) :=
      eraRadialFailure_subset_of_budget (hb.trans hcap) hb _ ⟨hf.1, hf.2.resolve_left (not_not.mpr hl)⟩
    have H := (mem_restartShearCommonFailureSection_iff ha hε.2 hl).mpr hbad
    exact Or.inl (Or.inl (by simpa [signedShearLogCoordinates] using H))
  · have hm : a ^ P < min (z 1) (z 2) := lt_of_not_ge (fun H => hl ⟨h₂, h₃, H⟩)
    apply Or.inr
    simpa [signedShearLogCoordinates, abs_of_pos hr, Real.exp_log hz.1,
      Real.exp_log hz.2.1, shearUnselectedSection, shearSectionLayer] using
      (show (z 0 ∈ Icc a (2 * a) ∧ z 1 ≤ 2 * ε * a ∧ z 2 ≤ 2 * ε * a) ∧
        a ^ P < z 1 ∧ a ^ P < z 2 from
        ⟨⟨⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩, h₂.2, h₃.2⟩, (lt_min_iff.mp hm).1, (lt_min_iff.mp hm).2⟩)

/-- The angular comparison retains the smaller-wall cutoff and the fixed original label. -/
theorem angularRadialFailure_subset_layer {h s a d L P η σ Bcap Bother : ℝ} {J : ℕ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hL : 0 ≤ L) (hP : 4 ≤ P)
    (hcap : Bcap ≤ 1) (hsmall : 51200 * (L + 1) * a ≤ Bcap)
    (other : Bool) {z : SectionCoordinates} (hz : z ∈ angularRadialDomain other a d L)
    (hf : z ∈ labelRadialFailure a (restartLabelSet L a P)
      (EraSurvivor.typicalDomain η J σ Bcap)
      (fun l r => (restartAmplitudeBudget L a l.2, restartReturnState h s l.1 l.2 r))) :
    orderedAngularLogCoordinates other z ∈
      mainWallSymmetrization (restartAngularFailureSection h s a L P η J σ Bother) ∪
        angularUnselectedSection a L P := by
  have hr : 0 < z 0 := ha.trans hz.2.2.1.1
  have ho : z 2 ≤ z 0 := by
    have H := hz.2.2.2.1
    cases other
    · exact H
    · exact le_of_lt H
  have hζ : 0 < z 2 ∧ z 2 < 2 * a := ⟨hz.2.1, ho.trans_lt hz.2.2.1.2⟩
  have hbase : scaledAngularLogCoordinates (1 / 2) z ∈
      mainWallSymmetrization (restartAngularFailureSection h s a L P η J σ Bother) ∪
        angularUnselectedSection a L P := by
    by_cases hl : (z 1, z 2) ∈ restartLabelSet L a P
    · have hb := (restartAmplitudeBudget_le_scale hL ha ha1 hP hl.2.2).trans hsmall
      have hbad : z 0 ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a (z 2)) Bother a (2 * a)
          (restartReturnState h s (z 1) (z 2)) :=
        eraRadialFailure_subset_of_budget (hb.trans hcap) hb _ ⟨hf.1, hf.2.resolve_left (not_not.mpr hl)⟩
      have H := (mem_restartAngularFailureSection_iff ha hz.1.le hζ hl.2.2 hr).mpr hbad
      exact Or.inl (Or.inl (by simpa [scaledAngularLogCoordinates] using H))
    · have hζlow : a ^ P < z 2 := lt_of_not_ge (fun H => hl ⟨hz.1.le, hz.2.1, H⟩)
      apply Or.inr
      have hθ := mul_le_mul_of_nonneg_right hz.1.le hr.le
      have heq : scaledAngularLogCoordinates (1 / 2) z = ![z 1 * z 0, -Real.log (z 0), -Real.log (z 2)] := by
        ext i
        fin_cases i <;> simp [scaledAngularLogCoordinates]
      rw [heq]
      change max (Real.exp (- -Real.log (z 0))) (Real.exp (- -Real.log (z 2))) ∈ Icc a (2 * a) ∧
        |z 1 * z 0| ≤ L * max (Real.exp (- -Real.log (z 0))) (Real.exp (- -Real.log (z 2))) ∧
        a ^ P < min (Real.exp (- -Real.log (z 0))) (Real.exp (- -Real.log (z 2)))
      simp only [neg_neg, Real.exp_log hr, Real.exp_log hz.2.1,
        max_eq_left ho, min_eq_right ho, abs_mul, abs_of_pos hr]
      exact ⟨⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩, hθ, hζlow⟩
  cases other
  · exact hbase
  · rcases hbase with hs | hu
    · exact Or.inl (mainWallReflection_mem_symmetrization_iff.mpr hs)
    · exact Or.inr ((angularUnselectedSection_reflection a L P _).mpr hu)

theorem radialFailureSet_subset_openSection {d ε : ℝ} (hd : 0 < d) (hε : ε ≤ 1)
    (F : RadialPieceIndex → Set SectionCoordinates) : radialFailureSet d ε F ⊆ mainWallOpenSection d := by
  rintro z (hb | hp)
  · exact hb.1
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact physicalRadialPiece_subset_openSection hd hε i (radialFailurePiece_subset d ε F i hi)

/-- Comparison caps need not agree: small actual budgets retain the identical statistical history. -/
theorem restartRadialFailureSet_subset_regions {h q d ε P η σ Bcap BA BS : ℝ} {J : ℕ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hε : 0 ≤ ε ∧ ε ≤ 1 / 128) (hL : 0 ≤ 1 / ε) (hP : 4 ≤ P)
    (hcap : Bcap ≤ 1) (hS : 800 * d ≤ Bcap) (hA : 51200 * (1 / ε + 1) * d ≤ Bcap) :
    radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap) ⊆
      mainWallRadialBoundary d ε ∪
        (angularFailureRegion h q d (1 / ε) P η J σ BA ∪ shearFailureRegion h q d ε P η J σ BS) := by
  rintro y (hb | hf)
  · exact Or.inl hb
  · apply Or.inr
    obtain ⟨⟨k, j⟩, z, ⟨hz, hbad⟩, rfl⟩ := mem_iUnion.mp hf
    have ha := dyadicScale_pos hd j
    have had := dyadicScale_le hd.le j
    have ha1 := had.trans hd1
    have hSa : 800 * dyadicScale d j ≤ Bcap :=
      (mul_le_mul_of_nonneg_left had (by norm_num)).trans hS
    have hAa : 51200 * (1 / ε + 1) * dyadicScale d j ≤ Bcap :=
      (mul_le_mul_of_nonneg_left had (by positivity)).trans hA
    rcases k with neg | other
    · have H : radialPieceMap (Sum.inl neg) z ∈
          mainWallSymmetrization (restartShearCommonFailureSection h
            (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) ε P η J σ BS) ∪
              shearUnselectedSection (dyadicScale d j) ε P := by
        cases neg
        · exact shearRadialFailure_subset_layer ha ha1 hε hP hcap hSa hz hbad
        · have H := shearRadialFailure_subset_layer (Bother := BS) ha ha1 hε hP hcap hSa
            (shearRadialDomain_swap hz) hbad
          have heq : radialPieceMap (Sum.inl true) z =
              mainWallReflection (signedShearLogCoordinates 1 ![z 0, z 2, z 1]) := by
            ext i
            fin_cases i <;> simp [radialPieceMap, signedShearLogCoordinates, mainWallReflection]
          rw [heq]
          rcases H with hs | hu
          · exact Or.inl (mainWallReflection_mem_symmetrization_iff.mpr hs)
          · exact Or.inr ((shearUnselectedSection_reflection _ _ _ _).mpr hu)
      rcases H with hs | hu
      · exact Or.inr (Or.inl (mem_iUnion_of_mem j hs))
      · exact Or.inr (Or.inr (mem_iUnion_of_mem j hu))
    · have H := angularRadialFailure_subset_layer (Bother := BA) ha ha1 hL hP hcap hAa other hz hbad
      rcases H with hs | hu
      · exact Or.inl (Or.inl (mem_iUnion_of_mem j hs))
      · exact Or.inl (Or.inr (mem_iUnion_of_mem j hu))

theorem mainWallOriginalMeasure_radialFailure_le_regions {h q d ε P η σ Bcap BA BS : ℝ} {J : ℕ}
    (hh : 0 < h) (hd : 0 < d) (hd1 : d ≤ 1) (hdh : d ≤ h)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 128) (hL : 0 ≤ 1 / ε) (hP : 4 ≤ P)
    (hcap : Bcap ≤ 1) (hS : 800 * d ≤ Bcap) (hA : 51200 * (1 / ε + 1) * d ≤ Bcap)
    (hE : MeasurableSet (radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap))) :
    mainWallOriginalMeasure h (radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap)) ≤
      ENNReal.ofReal (1 + 4 * h ^ 2) *
        (mainWallMeasure h (angularFailureRegion h q d (1 / ε) P η J σ BA) +
          mainWallMeasure h (shearFailureRegion h q d ε P η J σ BS)) := by
  have hsub := restartRadialFailureSet_subset_regions (h := h) (q := q) (η := η) (J := J)
    (σ := σ) (BA := BA) (BS := BS) hd hd1 hε hL hP hcap hS hA
  have hB : mainWallMeasure h (mainWallRadialBoundary d ε) = 0 :=
    (mainWallOriginalMeasure_null_iff hh _).mp (mainWallOriginalMeasure_radialBoundary h d ε)
  have H : mainWallMeasure h (radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap)) ≤
      mainWallMeasure h (angularFailureRegion h q d (1 / ε) P η J σ BA) +
        mainWallMeasure h (shearFailureRegion h q d ε P η J σ BS) := calc
    _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hB, zero_add]
    _ ≤ _ := measure_union_le _ _
  have hsmall := radialFailureSet_subset_openSection hd (by linarith only [hε.2] : ε ≤ 1)
    (restartRadialFailureFamily h q d ε P η J σ Bcap)
  have HO := mainWallOriginalMeasure_le_of_small_walls hh hE (fun z hz =>
    ⟨(le_max_left _ _).trans ((hsmall hz).2.le.trans hdh),
      (le_max_right _ _).trans ((hsmall hz).2.le.trans hdh)⟩)
  exact HO.trans (mul_le_mul' le_rfl H)

end BianchiIX
