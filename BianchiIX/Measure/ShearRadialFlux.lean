import BianchiIX.Dynamics.ShearSectionFlux
import BianchiIX.Statistics.ShearRestartEraStatistics

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def restartShearRadialFlux (h n₂ n₃ : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ ρ in A, ENNReal.ofReal (restartShearFluxDensity h n₂ n₃ ρ)

theorem restartShearRadialFlux_le {h a ε n₂ n₃ : ℝ} {A : Set ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1 / 8) (ha : 0 < a) (hah : a ≤ h / 8)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 64) (h₂ : 0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a)
    (h₃ : 0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) (hA : A ⊆ Icc a (2 * a)) :
    restartShearRadialFlux h n₂ n₃ A ≤ ENNReal.ofReal (3 * a) := by
  calc
    _ ≤ ∫⁻ ρ in Icc a (2 * a), ENNReal.ofReal (restartShearFluxDensity h n₂ n₃ ρ) :=
      lintegral_mono_set hA
    _ ≤ ∫⁻ _ in Icc a (2 * a), ENNReal.ofReal (3 : ℝ) :=
      setLIntegral_mono' measurableSet_Icc (fun ρ hρ =>
        ENNReal.ofReal_le_ofReal (restartShearFluxDensity_bounds hh hh1 ha hah hε h₂ h₃ hρ).2)
    _ = _ := by simp [Real.volume_Icc, show 2 * a - a = a by ring, ENNReal.ofReal_mul]

/-- The actual statistical failure on every shear radial slice has a clipped corrected-flux bound. -/
theorem exists_restartShear_failure_flux_slices (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ),
            ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
              ∀ n₂ n₃ : ℝ, (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P →
                let s := q / 2 * Real.log (1 / a)
                let B := restartShearAmplitudeBudget a n₂ n₃
                let F := eraRadialFailure η J σ B Bcap a (2 * a) (restartShearReturnState h s n₂ n₃)
                MeasurableSet F ∧ ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc a (2 * a) →
                  restartShearRadialFlux h n₂ n₃ (A ∩ F) ≤
                    ENNReal.ofReal (3 * min a (640 * Real.sqrt 3 * B ^ σ)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_era_statistics hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh q P hq hP
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  obtain ⟨aS, haS, HaS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  refine ⟨min aS (h / 8), lt_min haS (div_pos hh.1 (by norm_num)), ?_⟩
  intro a ha ε hε n₂ n₃ h₂ h₃ h₃P s B F
  have hah : a ≤ h / 8 := ha.2.trans (min_le_right _ _)
  obtain ⟨_, hF, Hloss, _⟩ := (HaS a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε hε).2 n₂ n₃ h₂ h₃ h₃P
  refine ⟨hF, ?_⟩
  intro A hA hAI
  have hweight (ρ : ℝ) (hρ : ρ ∈ A) :
      ENNReal.ofReal (restartShearFluxDensity h n₂ n₃ ρ) ≤ ENNReal.ofReal (3 : ℝ) :=
    ENNReal.ofReal_le_ofReal (restartShearFluxDensity_bounds hh.1 hh1 ha.1 hah hε
      ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ (hAI hρ)).2
  have H := (Hloss A hA hAI (fun ρ => ENNReal.ofReal (restartShearFluxDensity h n₂ n₃ ρ))
    3 (by norm_num) hweight).trans (min_le_right _ _)
  by_cases hmin : a ≤ 640 * Real.sqrt 3 * B ^ σ
  · rw [min_eq_left hmin]
    exact restartShearRadialFlux_le hh.1 hh1 ha.1 hah hε ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩
      (inter_subset_left.trans hAI)
  · rw [min_eq_right (le_of_not_ge hmin)]
    exact H.trans_eq (by congr 1; ring)

end BianchiIX
