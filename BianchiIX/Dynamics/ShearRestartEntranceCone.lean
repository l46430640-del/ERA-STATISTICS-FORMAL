import BianchiIX.Dynamics.EntranceWallCone
import BianchiIX.Dynamics.ShearRestartEntranceRadialResponse

noncomputable section

namespace BianchiIX

open Set

/-- Any prescribed square-root cone width is attained after the preceding entrance of the exact shear family. -/
theorem exists_restartShearEntrance_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η > (0 : ℝ),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
              let Z := fun t => entranceReturnState (Y t)
              let κ := fun t => coreRadius (Z t 0) (Z t 2)
              Y ρ 2 < 1 → DifferentiableAt ℝ Z ρ ∧ DifferentiableAt ℝ κ ρ ∧
              0 < -deriv κ ρ ∧ 0 < Z ρ 1 ∧ 0 < Z ρ 3 ∧
              |deriv (fun t => Z t 1) ρ| ≤ η * Real.sqrt (Z ρ 1) * |deriv κ ρ| ∧
              |deriv (fun t => Z t 3) ρ| ≤ η * Real.sqrt (Z ρ 3) * |deriv κ ρ| := by
  obtain ⟨C, hC, ε₀, hε₀, hε₀small, HC⟩ := exists_entrance_wall_sqrt_curve_bounds
  obtain ⟨hI, hhI, D, hD, HI⟩ := exists_restartShearEntrance_differential_inputs
  obtain ⟨hR, hhR, _, _, HR⟩ := exists_restartShearEntrance_radial_response
  refine ⟨min hI hR, lt_min hhI hhR, ?_⟩
  intro h hh q P hq hP η hη
  let E := 8388608 * C * D
  have hE : 0 < E := by dsimp only [E]; positivity
  let δ := min ε₀ ((η / E) ^ 2)
  have hδ : 0 < δ := lt_min hε₀ (sq_pos_of_pos (div_pos hη hE))
  have hδsmall : δ ≤ 1 / 10000 := (min_le_left _ _).trans hε₀small
  have hrootδ : Real.sqrt δ ≤ η / E := Real.sqrt_le_iff.mpr ⟨(div_pos hη hE).le, min_le_right _ _⟩
  have hEδ : E * Real.sqrt δ ≤ η := by
    have H := mul_le_mul_of_nonneg_left hrootδ hE.le
    simpa only [mul_div_cancel₀ _ hE.ne'] using H
  obtain ⟨aI, haI, HaI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
  refine ⟨min aI aR, lt_min haI haR, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y Z κ hv
  obtain ⟨HY, hk8, _, hkhi, hm, hu, hv', hw, _, Hd0, Hdwall⟩ :=
    HaI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨HK, _, _, _, _, _, Hlo, _⟩ :=
    HaR a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let k := coreRadius (Y ρ 0) (Y ρ 2)
  change 8 ≤ k at hk8
  change k ≤ 32 / a at hkhi
  change 1 / (8192 * a ^ 2) ≤ -deriv κ ρ at Hlo
  have hk0 : 0 < k := by linarith only [hk8]
  have hk' : 7 / 4 ≤ coreRadius (Y ρ 0) (Y ρ 2) := by change 7 / 4 ≤ k; linarith only [hk8]
  obtain ⟨HZ, hU, hW, HU, HW⟩ := HC Y ρ D HY hD.le hk' hm.le
    ⟨hu.1, hu.2.trans (min_le_left _ _)⟩ hv' ⟨hw.1, hw.2.trans (min_le_left _ _)⟩ Hd0 Hdwall
  change |deriv (fun t => Z t 1) ρ| ≤ C * D * k ^ 2 * Real.sqrt (Y ρ 1 * Y ρ 2) * Real.sqrt (Z ρ 1) at HU
  change |deriv (fun t => Z t 3) ρ| ≤ C * D * k * Real.sqrt (Y ρ 3 * Y ρ 2) * Real.sqrt (Z ρ 3) at HW
  have Hratio : k ^ 2 ≤ 8388608 * |deriv κ ρ| := by
    calc
      _ ≤ (32 / a) ^ 2 := pow_le_pow_left₀ hk0.le hkhi 2
      _ = 8388608 * (1 / (8192 * a ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Hlo.trans (neg_le_abs _)) (by norm_num)
  have Hroot {w : ℝ} (hw : 0 ≤ w ∧ w ≤ δ) : Real.sqrt (w * Y ρ 2) ≤ Real.sqrt δ :=
    Real.sqrt_le_sqrt ((mul_le_of_le_one_right hw.1 hv'.2.le).trans hw.2)
  have Hwall {x dx w : ℝ} (hw : 0 ≤ w ∧ w ≤ δ)
      (H : |dx| ≤ C * D * k ^ 2 * Real.sqrt (w * Y ρ 2) * Real.sqrt x) :
      |dx| ≤ η * Real.sqrt x * |deriv κ ρ| := by
    calc
      _ ≤ C * D * k ^ 2 * Real.sqrt δ * Real.sqrt x := H.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Hroot hw) (by positivity)) (Real.sqrt_nonneg x))
      _ ≤ C * D * (8388608 * |deriv κ ρ|) * Real.sqrt δ * Real.sqrt x := by gcongr
      _ = (E * Real.sqrt δ) * Real.sqrt x * |deriv κ ρ| := by dsimp only [E]; ring
      _ ≤ _ := by gcongr
  have HW' : |deriv (fun t => Z t 3) ρ| ≤ C * D * k ^ 2 * Real.sqrt (Y ρ 3 * Y ρ 2) * Real.sqrt (Z ρ 3) := by
    apply HW.trans
    gcongr
    nlinarith only [mul_le_mul_of_nonneg_left (show 1 ≤ k by linarith only [hk8]) hk0.le]
  exact ⟨HZ, HK, (by positivity [ha.1] : 0 < 1 / (8192 * a ^ 2)).trans_le Hlo,
    hU, hW, Hwall ⟨hu.1.le, hu.2⟩ HU, Hwall ⟨hw.1.le, hw.2⟩ HW'⟩

end BianchiIX
