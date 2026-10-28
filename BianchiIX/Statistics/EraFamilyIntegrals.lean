import BianchiIX.Measure.FiberwiseLoss
import BianchiIX.Statistics.EraRadialStatistics

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The same actual-state statistical set controls arbitrary measurable radial families and label measures. -/
theorem exists_era_radial_family_statistics {Λ : Type*} [MeasurableSpace Λ]
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧
          ∀ (B : Λ → ℝ) (Γ : Λ → EraCurve), (∀ l, B l ∈ Ioc 0 Bstar) →
            (∀ l, (Γ l).Admissible (B l)) →
            ∀ (a b : Λ → ℝ) (f : Λ → ℝ → ℝ) (Y : Λ × ℝ → CoreAngleState) (c : ℝ), 0 < c →
              (∀ l, ∀ r ∈ Icc (a l) (b l),
                DifferentiableAt ℝ (f l) r ∧ c ≤ deriv (f l) r ∧
                  f l r ∈ Ioo 0 1 ∧ (Γ l).state (2 / f l r) = Y (l, r)) →
              ∀ D : Set (Λ × ℝ), MeasurableSet D →
                Measurable (fun p : D => (B p.val.1, Y p.val)) →
                (∀ p ∈ D, p.2 ∈ Icc (a p.1) (b p.1)) →
                let F := D \ (fun p => (B p.1, Y p)) ⁻¹' EraSurvivor.typicalDomain η J σ Bcap
                MeasurableSet F ∧
                  (∀ p ∈ D, p ∉ F → ∃ q : eraSurvivorDomain η J σ Bcap,
                    q.val = (B p.1, Y p) ∧ EraStatistics (EraSurvivor.digits q) (EraSurvivor.phase q)) ∧
                  ∀ (μ : Measure Λ) (A : Set (Λ × ℝ)), MeasurableSet A → A ⊆ D →
                    ∀ ω : Λ × ℝ → ℝ≥0∞, Measurable ω → ∀ M : Λ → ℝ, (∀ l, 0 ≤ M l) →
                      (∀ p ∈ A, ω p ≤ ENNReal.ofReal (M p.1)) →
                      let L := fun l => ENNReal.ofReal (M l / c) * ENNReal.ofReal (80 * B l ^ σ)
                      (∫⁻ p in A ∩ F, ω p ∂μ.prod volume) ≤
                          ∫⁻ l, min (∫⁻ r in {r | (l, r) ∈ A}, ω (l, r)) (L l) ∂μ ∧
                        (∫⁻ l, min (∫⁻ r in {r | (l, r) ∈ A}, ω (l, r)) (L l) ∂μ) ≤
                          min (∫⁻ p in A, ω p ∂μ.prod volume) (∫⁻ l, L l ∂μ) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_joint_statistics hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, htyp, Bstar, hstar, hstarcap, Hstats⟩ :=
    Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, Bstar, hstar, hstarcap, ?_⟩
  intro B Γ hB hΓ a b f Y c hc Hradial D hD hY hDI F
  have hF : MeasurableSet F := by
    have heq : F = Subtype.val '' {p : D | (B p.val.1, Y p.val) ∉
        EraSurvivor.typicalDomain η J σ Bcap} := by
      ext p
      exact ⟨fun hp => ⟨⟨p, hp.1⟩, hp.2, rfl⟩, fun ⟨q, hq, heq⟩ => heq ▸ ⟨q.property, hq⟩⟩
    rw [heq]
    exact hD.subtype_image (htyp.compl.preimage hY)
  have Hcurve (l : Λ) := Hstats (B l) (hB l) (Γ l) (hΓ l)
  have Hfailure (l : Λ) := by
    have hloss : volume (Ioo 0 1 \ EraSurvivor.curveTypicalSet (Γ l) η J σ (B l) Bcap) ≤
        ENNReal.ofReal (80 * B l ^ σ) := by
      simpa only [univ_inter] using ((Hcurve l).2.2.1 univ).trans (min_le_right _ _)
    exact era_radial_failure_weighted hc
      (fun r hr => (Hradial l r hr).1) (fun r hr => (Hradial l r hr).2.1)
      (fun r hr => (Hradial l r hr).2.2.1) (fun r hr => (Hradial l r hr).2.2.2)
      (Hcurve l).1 hloss
  refine ⟨hF, ?_, ?_⟩
  · intro p hp hnot
    have hgood : (B p.1, Y p) ∈ EraSurvivor.typicalDomain η J σ Bcap := by
      by_contra hn
      exact hnot ⟨hp, hn⟩
    have hmatch := (Hradial p.1 p.2 (hDI p hp)).2.2.2
    have hfgood := (era_radial_good_iff (Hradial p.1 p.2 (hDI p hp)).2.2.1 hmatch).mpr hgood
    obtain ⟨q, hq, hstat⟩ := (Hcurve p.1).2.2.2 (f p.1 p.2) hfgood
    exact ⟨q, hq.trans (congrArg (fun Z => (B p.1, Z)) hmatch), hstat⟩
  · intro μ A hA hAD ω hω M hM hbound L
    apply fiberwise_loss_integral hA hF hω
    apply Filter.Eventually.of_forall
    intro l
    let Al : Set ℝ := {r | (l, r) ∈ A}
    have hAl : MeasurableSet Al := hA.preimage measurable_prodMk_left
    have hAlI : Al ⊆ Icc (a l) (b l) := fun r hr => hDI (l, r) (hAD hr)
    have heq : {r | (l, r) ∈ A ∩ F} = Al ∩
        eraRadialFailure η J σ (B l) Bcap (a l) (b l) (fun r => Y (l, r)) := by
      ext r
      constructor
      · rintro ⟨hrA, hrD, hrbad⟩
        exact ⟨hrA, hDI (l, r) hrD, hrbad⟩
      · rintro ⟨hrA, _, hrbad⟩
        exact ⟨hrA, hAD hrA, hrbad⟩
    rw [heq]
    exact (Hfailure l).2 Al hAl hAlI (fun r => ω (l, r)) (M l) (hM l)
      (fun r hr => hbound (l, r) hr)

end BianchiIX
