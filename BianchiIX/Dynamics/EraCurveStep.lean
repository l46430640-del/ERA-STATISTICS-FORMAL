import BianchiIX.Dynamics.EraRetainedPhases
import BianchiIX.Dynamics.EraAmplitudeExtension

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

structure EraCurve where
  U : ℝ → ℝ
  W : ℝ → ℝ

namespace EraCurve

def state (Γ : EraCurve) (r : ℝ) : CoreAngleState := ![r, Γ.U r, Γ.W r]

def Admissible (Γ : EraCurve) (B : ℝ) : Prop :=
  ∀ r : ℝ, 2 < r → 0 < Γ.U r ∧ 0 < Γ.W r ∧ Γ.U r + Γ.W r ≤ B ∧
    ContDiffAt ℝ 1 Γ.U r ∧ ContDiffAt ℝ 1 Γ.W r ∧
    |deriv Γ.U r| ≤ Real.sqrt (Γ.U r) ∧ |deriv Γ.W r| ≤ Real.sqrt (Γ.W r)

def successor (Γ : EraCurve) (η : ℝ) (J m : ℕ) (β : ℝ) : EraCurve :=
  ⟨eraAmplitudeExtension η J m β Γ.U Γ.W 1, eraAmplitudeExtension η J m β Γ.U Γ.W 3⟩

/-- Uniform data for one actual era, its selected inverse branches, and its successor curves. -/
structure StepEstimates (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B C : ℝ) : Prop where
  beta_pos : 0 < B ^ σ
  beta_small : B ^ σ < 1 / 160
  branch : ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ →
    let h := eraInverseBranch η J m (B ^ σ) Γ.U Γ.W
    let K := Icc (2 * B ^ σ) (1 - 2 * B ^ σ)
    StrictAntiOn h K ∧ ∀ y ∈ K,
      h y ∈ Ioo (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)) ∧
      graphPhase (eraBoundedPhase η J m) Γ.U Γ.W (2 / h y) = y ∧
      ContDiffAt ℝ 1 h y ∧ deriv h y < 0 ∧
      |h y - gaussInv ((m : ℝ) + 1) y| ≤ C * B / ((m : ℝ) + 1) ^ 2 ∧
      |Real.log (|deriv h y| / |deriv (gaussInv ((m : ℝ) + 1)) y|)| ≤ 5 * C * Real.sqrt B
  successor_admissible : ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ →
    (Γ.successor η J m (B ^ σ)).Admissible (B ^ (4 / 3 : ℝ))
  successor_match : ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ → ∀ y ∈ Icc (2 * B ^ σ) (1 - 2 * B ^ σ),
    let x := 2 / eraInverseBranch η J m (B ^ σ) Γ.U Γ.W y
    eraOutputRadius η J m (Γ.state x) = 2 / y ∧
      (Γ.successor η J m (B ^ σ)).U (2 / y) = eraOutputState η J m (Γ.state x) 1 ∧
      (Γ.successor η J m (B ^ σ)).W (2 / y) = eraOutputState η J m (Γ.state x) 3
  branch_disjoint : (↑(Finset.range ⌊1 / B ^ σ⌋₊) : Set ℕ).PairwiseDisjoint
    (fun m => Ioo (eraInverseBranch η J m (B ^ σ) Γ.U Γ.W (1 - 2 * B ^ σ))
      (eraInverseBranch η J m (B ^ σ) Γ.U Γ.W (2 * B ^ σ)))
  stopped_volume : volume (Ioo (0 : ℝ) 1 \ eraRetainedPhases η J ⌊1 / B ^ σ⌋₊ (B ^ σ) Γ.U Γ.W) ≤
    ENNReal.ofReal (10 * B ^ σ)

theorem StepEstimates.branch_image_open {Γ : EraCurve} {η σ B C : ℝ} {J : ℕ}
    (H : Γ.StepEstimates η J σ B C) (m : ℕ) (hm : m < ⌊1 / B ^ σ⌋₊) :
    eraInverseBranch η J m (B ^ σ) Γ.U Γ.W '' Ioo (2 * B ^ σ) (1 - 2 * B ^ σ) =
      Ioo (eraInverseBranch η J m (B ^ σ) Γ.U Γ.W (1 - 2 * B ^ σ))
        (eraInverseBranch η J m (B ^ σ) Γ.U Γ.W (2 * B ^ σ)) := by
  have hc : ContinuousOn (eraInverseBranch η J m (B ^ σ) Γ.U Γ.W)
      (Icc (2 * B ^ σ) (1 - 2 * B ^ σ)) :=
    fun y hy => ((H.branch m hm).2 y hy).2.2.1.continuousAt.continuousWithinAt
  exact hc.image_Ioo_of_strictAntiOn (by linarith [H.beta_small]) (H.branch m hm).1

end EraCurve

/-- The actual inverse branches, successor curves, and stopping loss hold at one common amplitude scale. -/
theorem exists_era_curve_step :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ C ≥ (1 : ℝ), ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B → Γ.StepEstimates η J σ B C := by
  obtain ⟨δl, hδl, hδlmax, HL⟩ := exists_era_retained_phase_loss
  obtain ⟨δe, hδe, _, HE⟩ := exists_era_amplitude_extension
  refine ⟨min δl δe, lt_min hδl hδe, (min_le_left _ _).trans hδlmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bl, hBl, hBlone, Hloss⟩ :=
    HL η hη (hηδ.trans (min_le_left _ _)) J (by omega) σ hσ hσone hσJ
  obtain ⟨ε, hε, _, A, hA, Hextend⟩ := HE η hη (hηδ.trans (min_le_right _ _)) J hJ
  obtain ⟨Be, hBe, _, Hbudget⟩ := exists_retained_era_parameter_budget hε
    (by linarith : 0 ≤ A) hσ hσone hσJ
  refine ⟨C, hC, min Bl Be, lt_min hBl hBe, (min_le_left _ _).trans_lt hBlone, ?_⟩
  intro B hB Γ hΓ
  obtain ⟨hβ, hβmax, Hbranch, Hdisjoint, _, hvol⟩ :=
    Hloss B ⟨hB.1, hB.2.trans (min_le_left _ _)⟩ Γ.U Γ.W hΓ
  obtain ⟨_, _, hsmall, hmargin, hscale⟩ := Hbudget B ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
  have Hext (m : ℕ) (hm : m < ⌊1 / B ^ σ⌋₊) := Hextend m (B ^ σ) B Γ.U Γ.W hβ
    (by linarith) (hscale m (by
      have Hcast : (m : ℝ) + 1 ≤ (⌊1 / B ^ σ⌋₊ : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hm)
      exact Hcast.trans (Nat.floor_le (by positivity)))) hsmall hmargin (by
        intro r hr
        apply hΓ r
        nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m])
  refine ⟨hβ, hβmax, ?_, ?_, ?_, Hdisjoint, hvol⟩
  · intro m hm
    exact ⟨(Hbranch m (Finset.mem_range.mpr hm)).1, (Hbranch m (Finset.mem_range.mpr hm)).2.2⟩
  · intro m hm r _
    obtain ⟨hθ, hcu, hcw, _, Hb⟩ := Hext m hm
    obtain ⟨hu, hw, hsum, hdu, hdw⟩ := Hb r
    exact ⟨hu, hw, hsum, hcu.contDiffAt, hcw.contDiffAt,
      hdu.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) (by linarith)),
      hdw.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) (by linarith))⟩
  · intro m hm y hy
    obtain ⟨_, _, _, Hmatch, _⟩ := Hext m hm
    obtain ⟨hk, hu, hw, _, _⟩ := Hmatch y hy
    let g := intervalRadiusInverse (graphPhase (eraBoundedPhase η J m) Γ.U Γ.W)
      (2 * ((m : ℝ) + 1 + B ^ σ)) (2 * ((m : ℝ) + 2 - B ^ σ))
    have hrec : g y = 2 / eraInverseBranch η J m (B ^ σ) Γ.U Γ.W y := by
      change g y = 2 / (2 / g y)
      field_simp
    change eraOutputRadius η J m (Γ.state (g y)) = 2 / y at hk
    change (Γ.successor η J m (B ^ σ)).U (2 / y) = eraOutputState η J m (Γ.state (g y)) 1 at hu
    change (Γ.successor η J m (B ^ σ)).W (2 / y) = eraOutputState η J m (Γ.state (g y)) 3 at hw
    rw [hrec] at hk hu hw
    exact ⟨hk, hu, hw⟩

end BianchiIX
