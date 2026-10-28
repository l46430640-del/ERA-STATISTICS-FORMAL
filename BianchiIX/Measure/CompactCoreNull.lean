import BianchiIX.Statistics.CompactEraSurvival
import BianchiIX.Measure.CoreBoundedDigits

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def curveCompactEraHistories (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) (N : ℕ) (γ : ℝ) : Set ℝ :=
  {x | x ∈ Ioo (0 : ℝ) 1 ∧ compactEraHistories η J σ Bcap N γ (B, Γ.state (2 / x))}

def coreCompactEraHistories (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) (N : ℕ) (γ : ℝ) : Set CoreAngleState :=
  {q | q 0 ∈ Ioo (0 : ℝ) 1 ∧ 0 < q 1 ∧ 0 < q 2 ∧ q 1 + q 2 ≤ B ∧
    compactEraHistories η J σ Bcap N γ (B, ![2 / q 0, q 1, q 2])}

theorem curveCompactEraHistories_subset_boundedDigits {η σ B Bcap γ : ℝ} {J N : ℕ} {Γ : EraCurve}
    (hΓ : Γ.Admissible B)
    (H : ∀ X : CoreAngleState, 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
      compactEraHistories η J σ Bcap N γ (B, X) → (B, X) ∈ EraSurvivor.boundedDigitDomain η J σ Bcap) :
    curveCompactEraHistories Γ η J σ B Bcap N γ ⊆ EraSurvivor.curveBoundedDigits Γ η J σ B Bcap := by
  intro x hx
  have hr : 2 < 2 / x := (lt_div_iff₀ hx.1.1).mpr (by linarith only [hx.1.2])
  obtain ⟨hu, hw, hsum, _⟩ := hΓ (2 / x) hr
  exact ⟨hx.1, H _ hu hw hsum hx.2⟩

theorem coreCompactEraHistories_subset_boundedDigits {η σ B Bcap γ : ℝ} {J N : ℕ}
    (H : ∀ X : CoreAngleState, 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
      compactEraHistories η J σ Bcap N γ (B, X) → (B, X) ∈ EraSurvivor.boundedDigitDomain η J σ Bcap) :
    coreCompactEraHistories η J σ B Bcap N γ ⊆ coreBoundedDigits η J σ B Bcap := by
  intro q hq
  exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1,
    H _ hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2⟩

/-- Compactness along existing finite histories forces survival and gives zero measure on curves and core coordinates. -/
theorem exists_compactEra_null (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧
          ∀ N : ℕ, ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
            ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ ∀ B ∈ Ioc 0 Bstar,
              (∀ Γ : EraCurve, Γ.Admissible B →
                volume (curveCompactEraHistories Γ η J σ B Bcap N γ) = 0) ∧
              volume (coreCompactEraHistories η J σ B Bcap N γ) = 0 := by
  obtain ⟨δs, hδs, hδmax, HS⟩ := exists_compactEra_survival
  obtain ⟨δb, hδb, _, HB⟩ := exists_era_curve_boundedDigits_zero hBirkhoff
  refine ⟨min δs δb, lt_min hδs hδb, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hjoint, Bb, hBb, hBbcap, Hb⟩ :=
    HB η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, ?_⟩
  intro N γ hγ hγmax
  obtain ⟨Bs, hBs, _, _, Hs⟩ := HS η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
    N γ hγ hγmax Bcap hcap
  refine ⟨min Bs Bb, lt_min hBs hBb, (min_le_right _ _).trans hBbcap, ?_⟩
  intro B hB
  have hBb' : B ∈ Ioc 0 Bb := ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
  have H (X : CoreAngleState) : 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
      compactEraHistories η J σ Bcap N γ (B, X) → (B, X) ∈ EraSurvivor.boundedDigitDomain η J σ Bcap :=
    Hs (B, X) ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  refine ⟨?_, measure_mono_null (coreCompactEraHistories_subset_boundedDigits H)
    (volume_coreBoundedDigits_zero hjoint (Hb B hBb'))⟩
  intro Γ hΓ
  exact measure_mono_null (curveCompactEraHistories_subset_boundedDigits hΓ H) (Hb B hBb' Γ hΓ)

end BianchiIX
