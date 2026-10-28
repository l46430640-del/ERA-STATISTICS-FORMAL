import BianchiIX.Dynamics.EraCurveStep
import BianchiIX.Analysis.AmplitudeSequence
import Mathlib.Data.PNat.Basic

noncomputable section

namespace BianchiIX

open Set

namespace EraCurve

def constant (B : ℝ) : EraCurve := ⟨fun _ => B / 2, fun _ => B / 2⟩

theorem constant_admissible {B : ℝ} (hB : 0 < B) : (constant B).Admissible B := by
  intro r _
  refine ⟨half_pos hB, half_pos hB, by dsimp [constant]; linarith,
    contDiffAt_const, contDiffAt_const, ?_, ?_⟩ <;>
    simpa only [constant, deriv_const, abs_zero] using Real.sqrt_nonneg (B / 2)

/-- Unretained digits have empty branch domains; a constant curve makes their unused descendants total. -/
def nextCurve (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) (a : ℕ+) : EraCurve :=
  if a.natPred < ⌊1 / B ^ σ⌋₊ then Γ.successor η J a.natPred (B ^ σ)
  else constant (B ^ (4 / 3 : ℝ))

def family (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) (w : List ℕ+) : EraCurve :=
  w.reverseRecOn Γ (fun v a γ => γ.nextCurve η J σ (eraAmplitude B v.length) a)

@[simp] theorem family_nil (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) :
    Γ.family η J σ B [] = Γ := by simp [family, List.reverseRecOn]

@[simp] theorem family_append (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ) (w : List ℕ+) (a : ℕ+) :
    Γ.family η J σ B (w ++ [a]) =
      (Γ.family η J σ B w).nextCurve η J σ (eraAmplitude B w.length) a := by
  simp [family, List.reverseRecOn]

theorem family_append_of_retained (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B : ℝ)
    (w : List ℕ+) (a : ℕ+) (ha : a.natPred < ⌊1 / (eraAmplitude B w.length) ^ σ⌋₊) :
    Γ.family η J σ B (w ++ [a]) =
      (Γ.family η J σ B w).successor η J a.natPred ((eraAmplitude B w.length) ^ σ) := by
  rw [family_append, nextCurve, if_pos ha]

theorem family_admissible {η σ B Bstar C : ℝ} {J : ℕ} {Γ : EraCurve}
    (hB : B ∈ Ioc 0 Bstar) (hBs : Bstar ≤ 1) (hΓ : Γ.Admissible B)
    (H : ∀ b ∈ Ioc 0 Bstar, ∀ γ : EraCurve, γ.Admissible b → γ.StepEstimates η J σ b C)
    (w : List ℕ+) : (Γ.family η J σ B w).Admissible (eraAmplitude B w.length) := by
  have hb (n : ℕ) : eraAmplitude B n ∈ Ioc 0 Bstar :=
    ⟨eraAmplitude_pos hB.1 n, (eraAmplitude_le hB.1.le (hB.2.trans hBs) n).trans hB.2⟩
  induction w using List.reverseRecOn with
  | nil => simpa using hΓ
  | append_singleton w a ih =>
    rw [family_append, List.length_append, List.length_singleton, eraAmplitude_succ hB.1.le]
    unfold nextCurve
    split_ifs with ha
    · exact (H _ (hb w.length) _ ih).successor_admissible a.natPred ha
    · exact constant_admissible (Real.rpow_pos_of_pos (hb w.length).1 _)

end EraCurve

/-- The actual successors define admissible curves with uniform step estimates at every finite word. -/
theorem exists_era_curve_family :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ C ≥ (1 : ℝ), ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B → ∀ w : List ℕ+,
            (Γ.family η J σ B w).Admissible (eraAmplitude B w.length) ∧
            (Γ.family η J σ B w).StepEstimates η J σ (eraAmplitude B w.length) C := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_curve_step
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bs, hBs, hBsone, H⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨C, hC, Bs, hBs, hBsone, ?_⟩
  intro B hB Γ hΓ w
  have ha := EraCurve.family_admissible hB hBsone.le hΓ H w
  exact ⟨ha, H _ ⟨eraAmplitude_pos hB.1 _,
    (eraAmplitude_le hB.1.le (hB.2.trans hBsone.le) _).trans hB.2⟩ _ ha⟩

end BianchiIX
