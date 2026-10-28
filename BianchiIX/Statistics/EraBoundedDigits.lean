import BianchiIX.Statistics.GaussBoundedDigits
import BianchiIX.Statistics.EraCodingRealization

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace EraSurvivor

def boundedDigitDomain (η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set (ℝ × CoreAngleState) :=
  Subtype.val '' {p : eraSurvivorDomain η J σ Bcap | ∃ N : ℕ, ∀ n, (digits p n : ℕ) ≤ N}

theorem boundedDigitDomain_measurable {η σ Bcap : ℝ} {J : ℕ}
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bcap m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bcap m => eraBudgetReturn η J m p.val)) :
    MeasurableSet (boundedDigitDomain η J σ Bcap) := by
  apply (eraSurvivorDomain_measurable H).subtype_image
  simp only [ofPred_exists, ofPred_forall]
  exact MeasurableSet.iUnion (fun N => MeasurableSet.iInter (fun n =>
    measurableSet_le (measurable_subtype_coe.comp ((measurable_pi_apply n).comp (digits_measurable H))) measurable_const))

def curveBoundedDigits (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) : Set ℝ :=
  Ioo 0 1 ∩ (fun x => (B, Γ.state (2 / x))) ⁻¹' boundedDigitDomain η J σ Bcap

end EraSurvivor

namespace EraCurve.Realization

/-- Local coding distortion excludes every bounded digit sequence on an actual survivor curve. -/
theorem volume_curveBoundedDigits_zero {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ}
    {T : InverseBranchTree} (R : Γ.Realization η J σ B Bcap T)
    {d e : ℕ → ℝ} (E : T.BranchEstimates d e)
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    volume (EraSurvivor.curveBoundedDigits Γ η J σ B Bcap) = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [E.typicalSurvivors_ae_eq hBirkhoff hbudget] with x hx
  rintro ⟨hxunit, p, hp, hpx⟩
  change p.val = (B, Γ.state (2 / x)) at hpx
  have hxroot : x ∈ T.root := by rwa [R.root]
  have hps : (B, Γ.state (2 / x)) ∈ eraSurvivorDomain η J σ Bcap := by
    rw [← hpx]
    exact p.property
  let xt : T.survivors := ⟨x, (R.survivor_iff x hxroot).mp hps⟩
  have htyp : x ∈ T.typicalSurvivors := by
    change T.typicalSurvivors x
    rw [hx]
    exact xt.property
  have ht := (T.mem_typicalSurvivors xt).mp htyp
  have hdigits := R.digits_eq_tree xt p hpx
  change ∃ N : ℕ, ∀ n, (EraSurvivor.digits p n : ℕ) ≤ N at hp
  exact not_bounded_digits_of_typical ht (by simpa only [hdigits] using hp)

end EraCurve.Realization

/-- A single Borel set of actual states has zero bounded-digit measure on every small admissible curve. -/
theorem exists_era_curve_boundedDigits_zero (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ MeasurableSet (EraSurvivor.boundedDigitDomain η J σ Bcap) ∧
          ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ ∀ B ∈ Ioc 0 Bstar,
            ∀ Γ : EraCurve, Γ.Admissible B →
              volume (EraSurvivor.curveBoundedDigits Γ η J σ B Bcap) = 0 := by
  obtain ⟨δt, hδt, hδmax, HT⟩ := exists_era_curve_family
  obtain ⟨δs, hδs, _, HS⟩ := exists_era_selected_return
  refine ⟨min δt δs, lt_min hδt hδs, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bt, hBt, _, Htree⟩ := HT η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Bs, hBs, hBsone, Hmeas, Hselect⟩ := HS η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hCi : 0 ≤ 5 * C := mul_nonneg (by norm_num) hC0
  obtain ⟨Bb, hBb, _, Hbudget⟩ := exists_era_budget_threshold hσ hC0 hCi (show (0 : ℝ) ≤ 0 by rfl)
  refine ⟨Bs, hBs, hBsone, EraSurvivor.boundedDigitDomain_measurable Hmeas,
    min Bt (min Bs Bb), lt_min hBt (lt_min hBs hBb), (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro B hB Γ hΓ
  have hBt' : B ∈ Ioc 0 Bt := ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  have hBs' : B ∈ Ioc 0 Bs := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hBb' : B ∈ Ioc 0 Bb := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hnodes := Htree B hBt' Γ hΓ
  let T := Γ.inverseTree η J σ B C (fun w => (Hnodes w).2)
  have R : Γ.Realization η J σ B Bs T := EraCurve.realization_of_estimates hBs' hBsone.le Hnodes Hselect
  have E := EraCurve.inverseTree_estimates hB.1 hC0 (fun w => (Hnodes w).2)
  obtain ⟨hsmall, _, _⟩ := Hbudget B hBb'
  have hJreal : (2 : ℝ) ≤ (2 * J : ℕ) := by exact_mod_cast (show 2 ≤ 2 * J by omega)
  have hσhalf : σ ≤ 1 / 2 := by nlinarith only [hσJ, hJreal, hσ]
  exact R.volume_curveBoundedDigits_zero E hBirkhoff
    (era_distortion_budget hB.1 (hBs'.2.trans hBsone.le) hσ.le hσhalf hsmall hC0 hCi).2.2

end BianchiIX
