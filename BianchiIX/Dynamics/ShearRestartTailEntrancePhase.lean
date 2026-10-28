import BianchiIX.Dynamics.ShearRestartTailEntranceRadius
import BianchiIX.Analysis.ReciprocalRadialComparison
import BianchiIX.Analysis.ReciprocalRadialBounds

noncomputable section

namespace BianchiIX

open Set

def restartShearTailEntranceRadius (h a q D ζ ν ρ : ℝ) : ℝ :=
  let y := entranceReturnState (restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ)
  coreRadius (y 0) (y 2)

def restartShearTailEntrancePhase (h a q D ζ ν ρ : ℝ) : ℝ :=
  2 / restartShearTailEntranceRadius h a q D ζ ν ρ

/-- The first upward entrance after the long tail has the original reference phase and nondegenerate radius slope. -/
theorem exists_restartShearTail_entrance_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Φ := restartShearTailEntrancePhase h a q D ζ ν
            let F := restartShearTailEntranceRadius h a q D ζ ν
            let f₀ := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            entranceReturnValid (restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D) ρ) ∧
            DifferentiableAt ℝ Φ ρ ∧ |Φ ρ - f₀ ρ| ≤ C * a ^ 2 ∧
            |deriv Φ ρ - deriv f₀ ρ| ≤ C * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv Φ ρ ∧ deriv Φ ρ ≤ 2 / Real.sqrt 3 + 1 ∧
            DifferentiableAt ℝ F ρ ∧ 1 / (48 * a) ≤ F ρ ∧ F ρ ≤ 128 / a ∧
            1 / (36864 * a ^ 2) ≤ -deriv F ρ ∧ -deriv F ρ ≤ 24576 / a ^ 2 := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_entrance_radius
  obtain ⟨hG, hhG, HG⟩ := exists_restartShearTail_projection_phase
  refine ⟨min hR (min hG (1 / 16)), lt_min hhR (lt_min hhG (by norm_num)), ?_⟩
  intro h hh q D hq hD
  obtain ⟨B, hB, HB⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨K, hK, HK⟩ := HG h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q D hq hD
  let A := 2 * 48 ^ 2 * B + 4 * 6144 * 48 ^ 3 * B
  let C := A + K
  have hA : 0 < A := by dsimp only [A]; positivity
  have hC : 0 < C := add_pos hA hK
  have hvalue : 2 * 48 ^ 2 * B ≤ A := by dsimp only [A]; linarith only [hB]
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨aR, haR, HAR⟩ := HB P hP
  obtain ⟨aG, haG, HAG⟩ := HK P hP
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  refine ⟨min aR (min aG (min 1 (1 / (4 * Real.sqrt 3 * C)))),
    lt_min haR (lt_min haG (lt_min zero_lt_one (by positivity))), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Φ F f₀
  let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
  let k := fun r => coreRadius (Y r 0) (Y r 2)
  let f := restartShearTailProjectionPhase h a q ζ ν (shearTailTime a D)
  have ha1 : a ≤ 1 := ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨Hvalid, _, _, HFD, HkD, HFlo, HFhi, Hklo, Hrv, Hrd, Hkd⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, HfD, Hfv, Hfd, _, _⟩ :=
    HAG a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε hζ hν ρ hρ
  have HF0 : 0 < F ρ := (by positivity [ha.1] : 0 < 1 / (48 * a)).trans_le HFlo
  have HΦD : DifferentiableAt ℝ Φ ρ :=
    ((hasDerivAt_const ρ (2 : ℝ)).div HFD.hasDerivAt HF0.ne').differentiableAt
  have Hrv' : |F ρ - k ρ| ≤ B := Hrv.trans (mul_le_of_le_one_right hB.le ha1)
  obtain ⟨_, HV, HD⟩ := reciprocal_radial_comparison ha.1 (by norm_num : (0 : ℝ) < 48)
    (by norm_num : (0 : ℝ) ≤ 6144) HFD HkD HFlo Hklo Hrv' Hkd Hrd
  change |Φ ρ - f ρ| ≤ 2 * 48 ^ 2 * B * a ^ 2 at HV
  change |deriv (fun r => Φ r - f r) ρ| ≤ A * a at HD
  rw [deriv_fun_sub HΦD HfD] at HD
  have HV' := HV.trans (mul_le_mul_of_nonneg_right hvalue (sq_nonneg a))
  have Hval : |Φ ρ - f₀ ρ| ≤ C * a ^ 2 :=
    (abs_sub_le _ _ _).trans ((add_le_add HV' Hfv).trans_eq (by dsimp only [C]; ring))
  have Hder : |deriv Φ ρ - deriv f₀ ρ| ≤ C * a :=
    (abs_sub_le _ _ _).trans ((add_le_add HD Hfd).trans_eq (by dsimp only [C]; ring))
  have Href := restartReferenceRadialPhase_shear_derivative
    ⟨hh.1.le, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    ha.1 hρ (by norm_num : |(1 : ℝ)| = 1) ⟨hε.1, by linarith only [hε.2]⟩
    ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩
  have hCa : C * a ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * C)).mp
      (ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  have Hlo : 1 / (4 * Real.sqrt 3) ≤ deriv Φ ρ := by
    have he : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [he] at Href
    linarith only [(abs_le.mp Hder).1, Href.2.1, hCa]
  have Hhi : deriv Φ ρ ≤ 2 / Real.sqrt 3 + 1 := by
    linarith only [(abs_le.mp Hder).2, Href.2.2, hCa, hquarter]
  have HΦlo : (a / 4) / 16 ≤ Φ ρ := by
    calc
      _ = 2 / (128 / a) := by field_simp [ha.1.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) HF0 HFhi
  have HΦhi : Φ ρ ≤ 384 * (a / 4) := by
    calc
      _ ≤ 2 / (1 / (48 * a)) := div_le_div_of_nonneg_left (by norm_num) (by positivity [ha.1]) HFlo
      _ = _ := by field_simp [ha.1.ne']; ring
  have HDlo : 1 / 8 ≤ deriv Φ ρ := by
    have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
    exact ((le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
      (by linarith only [hsqrt2])).trans Hlo
  have HDhi : deriv Φ ρ ≤ 3 := by
    have H := div_le_self (by norm_num : (0 : ℝ) ≤ 2) hsqrt1
    linarith only [H, Hhi]
  obtain ⟨_, _, _, HFlod, HFhid⟩ := reciprocal_radial_bounds (by positivity [ha.1] : 0 < a / 4)
    (by norm_num : (0 : ℝ) ≤ 3) HΦD HΦlo HΦhi HDlo HDhi
  have heq : (fun r => 2 / Φ r) = F := by
    funext r
    change 2 / (2 / F r) = F r
    simp
  rw [heq] at HFlod HFhid
  refine ⟨Hvalid, HΦD, Hval, Hder, Hlo, Hhi, HFD, HFlo, HFhi, ?_, ?_⟩
  · convert! HFlod using 1
    ring
  · convert! HFhid using 1
    ring

end BianchiIX
