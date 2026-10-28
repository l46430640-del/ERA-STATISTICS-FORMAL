import BianchiIX.Measure.RadialPartitionFlux
import BianchiIX.Statistics.EraRadialStatistics
import BianchiIX.Dynamics.RestartStatisticalPreparation
import BianchiIX.Dynamics.ShearRestartCommonPreparation

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def labelRadialFailure (a : ℝ) (L : Set (ℝ × ℝ)) (G : Set (ℝ × CoreAngleState))
    (Z : (ℝ × ℝ) → ℝ → ℝ × CoreAngleState) : Set SectionCoordinates :=
  {z | z 0 ∈ Icc a (2 * a) ∧ ((z 1, z 2) ∉ L ∨ Z (z 1, z 2) (z 0) ∉ G)}

/-- Unselected labels fail everywhere; selected labels use the same joint actual-state typical set. -/
theorem measurableSet_labelRadialFailure {a : ℝ} {L : Set (ℝ × ℝ)}
    {G : Set (ℝ × CoreAngleState)} {Z : (ℝ × ℝ) → ℝ → ℝ × CoreAngleState}
    (hL : MeasurableSet L) (hG : MeasurableSet G)
    (hZ : Measurable (fun p : L × Icc a (2 * a) => Z p.1.val p.2.val)) :
    MeasurableSet (labelRadialFailure a L G Z) := by
  let D : Set SectionCoordinates := {z | (z 1, z 2) ∈ L ∧ z 0 ∈ Icc a (2 * a)}
  have hl : Measurable (fun z : SectionCoordinates => (z 1, z 2)) := by fun_prop
  have hD : MeasurableSet D := (hL.preimage hl).inter
    (measurableSet_Icc.preimage (measurable_pi_apply 0))
  let f : D → L × Icc a (2 * a) := fun z =>
    (⟨(z.val 1, z.val 2), z.property.1⟩, ⟨z.val 0, z.property.2⟩)
  have hf : Measurable f := by
    apply Measurable.prodMk
    · exact (hl.comp measurable_subtype_coe).subtype_mk
    · exact ((measurable_pi_apply 0).comp measurable_subtype_coe).subtype_mk
  have H := hD.subtype_image (hG.compl.preimage (hZ.comp hf))
  have heq : Subtype.val '' (fun z : D => Z (z.val 1, z.val 2) (z.val 0)) ⁻¹' Gᶜ =
      {z : SectionCoordinates | (z 1, z 2) ∈ L ∧ z 0 ∈ Icc a (2 * a) ∧ Z (z 1, z 2) (z 0) ∉ G} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property.1, w.property.2, hw⟩
    · rintro ⟨hl', hr, hg⟩
      exact ⟨⟨z, hl', hr⟩, hg, rfl⟩
  change MeasurableSet (Subtype.val '' (fun z : D => Z (z.val 1, z.val 2) (z.val 0)) ⁻¹' Gᶜ) at H
  rw [heq] at H
  have hU : MeasurableSet {z : SectionCoordinates | z 0 ∈ Icc a (2 * a) ∧ (z 1, z 2) ∉ L} :=
    (measurableSet_Icc.preimage (measurable_pi_apply 0)).inter (hL.preimage hl).compl
  convert! hU.union H using 1
  ext z
  simp only [labelRadialFailure, mem_union, mem_ofPred_eq]
  tauto

def restartRadialFailureFamily (h q d ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ)
    (i : RadialPieceIndex) : Set SectionCoordinates :=
  let a := dyadicScale d i.2
  let s := q / 2 * Real.log (1 / a)
  let G := EraSurvivor.typicalDomain η J σ Bcap
  match i.1 with
  | Sum.inl neg =>
      let F := labelRadialFailure a (restartShearCommonLabelSet ε a P) G
        (fun l r => (restartShearAmplitudeBudget a l.1 l.2, restartShearReturnState h s l.1 l.2 r))
      if neg then (fun z => ![z 0, z 2, z 1]) ⁻¹' F else F
  | Sum.inr _ =>
      labelRadialFailure a (restartLabelSet (1 / ε) a P) G
        (fun l r => (restartAmplitudeBudget (1 / ε) a l.2, restartReturnState h s l.1 l.2 r))

def restartRadialOutput (h q d ε : ℝ) (i : RadialPieceIndex) (z : SectionCoordinates) : ℝ × CoreAngleState :=
  let a := dyadicScale d i.2
  let s := q / 2 * Real.log (1 / a)
  match i.1 with
  | Sum.inl neg =>
      let l := if neg then (z 2, z 1) else (z 1, z 2)
      (restartShearAmplitudeBudget a l.1 l.2, restartShearReturnState h s l.1 l.2 (z 0))
  | Sum.inr _ => (restartAmplitudeBudget (1 / ε) a (z 2), restartReturnState h s (z 1) (z 2) (z 0))

theorem restartRadialFailure_good {h q d ε P η σ Bcap : ℝ} {J : ℕ}
    {i : RadialPieceIndex} {z : SectionCoordinates} (hz : z ∈ radialPieceDomain d ε i)
    (hn : z ∉ restartRadialFailureFamily h q d ε P η J σ Bcap i) :
    restartRadialOutput h q d ε i z ∈ EraSurvivor.typicalDomain η J σ Bcap := by
  by_contra hbad
  apply hn
  rcases i with ⟨neg | other, j⟩
  · have hr : z 0 ∈ Icc (dyadicScale d j) (2 * dyadicScale d j) :=
      ⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩
    cases neg <;> exact ⟨hr, Or.inr hbad⟩
  · exact ⟨⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩, Or.inr hbad⟩

theorem restartRadialFailureSet_success {h q d ε P η σ Bcap : ℝ} {J : ℕ}
    (hd : 0 < d) (hε : 0 < ε) (hε1 : ε ≤ 1) {z : SectionCoordinates}
    (hz : z ∈ mainWallOpenSection d \
      radialFailureSet d ε (restartRadialFailureFamily h q d ε P η J σ Bcap)) :
    ∃ i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧
      restartRadialOutput h q d ε i (radialPieceInverse i.1 z) ∈ EraSurvivor.typicalDomain η J σ Bcap := by
  obtain ⟨i, ⟨hi, hn⟩, _⟩ := radialFailureSet_complement hd hε hε1 _ hz
  refine ⟨i, hi, ?_⟩
  rcases hi with ⟨x, hx, rfl⟩
  rw [radialPieceInverse_map hd hx] at hn ⊢
  exact restartRadialFailure_good hx hn

/-- The selected and unselected statistical fibers instantiate the exact countable flux identity. -/
theorem exists_restartRadialFailure_partition (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 8 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ ε ∈ Ioc (0 : ℝ) (1 / 128), ∃ dstar > (0 : ℝ), dstar ≤ h / 8 ∧
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let F := restartRadialFailureFamily h q d ε P η J σ Bcap
                (∀ i, MeasurableSet (F i)) ∧ MeasurableSet (radialFailureSet d ε F) ∧
                  mainWallOriginalMeasure h (radialFailureSet d ε F) = (∑' i, radialFailureIntegral h d ε F i) ∧
                    (∀ z ∈ mainWallOpenSection d \ radialFailureSet d ε F,
                      ∃ i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧
                        restartRadialOutput h q d ε i (radialPieceInverse i.1 z) ∈
                          EraSurvivor.typicalDomain η J σ Bcap) ∧
                    ∀ i z, z ∈ radialPieceDomain d ε i → z ∉ F i →
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = restartRadialOutput h q d ε i z ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_joint_statistics hBirkhoff
  obtain ⟨hS, hhS, HS⟩ := exists_restartShear_common_statistical_preparation
  obtain ⟨hA, hhA, HA⟩ := exists_restart_statistical_preparation
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσ1 hσJ
  obtain ⟨Bcap, hcap, hcap1, hG, Bs, hBs, _, Hstats⟩ := Hδ η hη hηδ J hJ σ hσ hσ1 hσJ
  refine ⟨Bcap, hcap, hcap1, min hS (min hA (1 / 8)),
    lt_min hhS (lt_min hhA (by norm_num)), (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro h hh q D P hq hD hP ε hε
  have hh1 : h ≤ 1 / 8 := hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨aS, haS, HShear⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP Bs hBs
  obtain ⟨aA, haA, HAngle⟩ := HA h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    (1 / ε) (by positivity [hε.1]) q P hq (by linarith only [hD, hP]) Bs hBs
  refine ⟨min aS (min aA (h / 8)), lt_min haS (lt_min haA (div_pos hh.1 (by norm_num))),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro d hd F
  have hdh : d ≤ h / 8 := hd.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have HF : ∀ i, MeasurableSet (F i) := by
    rintro ⟨neg | other, j⟩
    · have ha : dyadicScale d j ∈ Ioc (0 : ℝ) aS :=
        ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd.2.trans (min_le_left _ _))⟩
      have H := measurableSet_labelRadialFailure
        (Z := fun l r => (restartShearAmplitudeBudget (dyadicScale d j) l.1 l.2,
          restartShearReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) l.1 l.2 r))
        (measurableSet_restartShearCommonLabelSet ε (dyadicScale d j) P) hG
        (HShear (dyadicScale d j) ha ε ⟨hε.1.le, hε.2⟩).1
      cases neg
      · exact H
      · exact H.preimage (by fun_prop)
    · have ha : dyadicScale d j ∈ Ioc (0 : ℝ) aA :=
        ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans
          (hd.2.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
      exact measurableSet_labelRadialFailure
        (Z := fun l r => (restartAmplitudeBudget (1 / ε) (dyadicScale d j) l.2,
          restartReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) l.1 l.2 r))
        (measurableSet_restartLabelSet (1 / ε) (dyadicScale d j) P) hG
        (HAngle (dyadicScale d j) ha).1
  refine ⟨HF, measurableSet_radialFailureSet hd.1 HF,
    mainWallOriginalMeasure_radialFailureSet hh.1 hh1 hd.1 hdh hε.1 (by linarith only [hε.2]) HF,
    (fun _ hz => restartRadialFailureSet_success hd.1 hε.1 (by linarith only [hε.2]) hz), ?_⟩
  have HShearStats (j : ℕ) (n₂ n₃ r : ℝ)
      (hl : (n₂, n₃) ∈ restartShearCommonLabelSet ε (dyadicScale d j) P)
      (hr : r ∈ Icc (dyadicScale d j) (2 * dyadicScale d j))
      (hg : (restartShearAmplitudeBudget (dyadicScale d j) n₂ n₃,
        restartShearReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) n₂ n₃ r) ∈
          EraSurvivor.typicalDomain η J σ Bcap) :
      ∃ p : eraSurvivorDomain η J σ Bcap,
        p.val = (restartShearAmplitudeBudget (dyadicScale d j) n₂ n₃,
          restartShearReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) n₂ n₃ r) ∧
        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by
    obtain ⟨hB, hΓ, Hrad⟩ := (HShear (dyadicScale d j)
      ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd.2.trans (min_le_left _ _))⟩
      ε ⟨hε.1.le, hε.2⟩).2 n₂ n₃ hl.1 hl.2.1 hl.2.2
    obtain ⟨_, _, _, Hgood⟩ := Hstats _ hB _ hΓ
    obtain ⟨p, hp, hs⟩ := Hgood _ ((era_radial_good_iff (Hrad r hr).1 (Hrad r hr).2.2.2).mpr hg)
    exact ⟨p, hp.trans (congrArg (fun Z => (_, Z)) (Hrad r hr).2.2.2), hs⟩
  rintro ⟨neg | other, j⟩ z hz hn
  · have hr : z 0 ∈ Icc (dyadicScale d j) (2 * dyadicScale d j) :=
      ⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩
    have hg := restartRadialFailure_good hz hn
    cases neg
    · exact HShearStats j (z 1) (z 2) (z 0)
        (by by_contra hl; exact hn ⟨hr, Or.inl hl⟩) hr hg
    · exact HShearStats j (z 2) (z 1) (z 0)
        (by by_contra hl; exact hn ⟨hr, Or.inl hl⟩) hr hg
  · have hr : z 0 ∈ Icc (dyadicScale d j) (2 * dyadicScale d j) :=
      ⟨hz.2.2.1.1.le, hz.2.2.1.2.le⟩
    have hl : (z 1, z 2) ∈ restartLabelSet (1 / ε) (dyadicScale d j) P := by
      by_contra hl
      exact hn ⟨hr, Or.inl hl⟩
    obtain ⟨hB, hΓ, Hrad⟩ := (HAngle (dyadicScale d j)
      ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans
        (hd.2.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩).2 (z 1) (z 2) hl.1 hl.2
    obtain ⟨_, _, _, Hgood⟩ := Hstats _ hB _ hΓ
    obtain ⟨p, hp, hs⟩ := Hgood _
      ((era_radial_good_iff (Hrad (z 0) hr).1 (Hrad (z 0) hr).2.2.2).mpr (restartRadialFailure_good hz hn))
    exact ⟨p, hp.trans (congrArg (fun Z => (_, Z)) (Hrad (z 0) hr).2.2.2), hs⟩

end BianchiIX
