import BianchiIX.Dynamics.ShearRestartTailWallBounds
import BianchiIX.Dynamics.ShearRestartTailEntrancePhase
import BianchiIX.Dynamics.EntranceWallCone

noncomputable section

namespace BianchiIX

open Set

/-- The actual entrance after the long tail has any prescribed square-root cone width, uniformly in both positive weak walls. -/
theorem exists_restartShearTail_entrance_cone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 2 < D → 6 * D + 2 < P → ∀ η > (0 : ℝ),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
          let Z := fun r => entranceReturnState (Y r)
          let κ := restartShearTailEntranceRadius h a q D ζ ν
          DifferentiableAt ℝ Z ρ ∧ DifferentiableAt ℝ κ ρ ∧
          0 < -deriv κ ρ ∧ 0 < Z ρ 1 ∧ 0 < Z ρ 3 ∧
          |deriv (fun r => Z r 1) ρ| ≤ η * Real.sqrt (Z ρ 1) * |deriv κ ρ| ∧
          |deriv (fun r => Z r 3) ρ| ≤ η * Real.sqrt (Z ρ 3) * |deriv κ ρ| := by
  obtain ⟨C, hC, δ, hδ, hδsmall, HC⟩ := exists_entrance_wall_sqrt_curve_bounds
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_entrance_inputs
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_entrance_phase
  obtain ⟨hW, hhW, HW⟩ := exists_restartShearTail_wall_bounds
  refine ⟨min hI (min hR hW), lt_min hhI (lt_min hhR hhW), ?_⟩
  intro h hh q D P hq hD hP η hη
  obtain ⟨B, hB, HBI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨_, _, HBR⟩ := HR h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q D hq hD
  let E := 150994944 * C * B
  have hE : 0 < E := by dsimp only [E]; positivity
  obtain ⟨aI, haI, HAI⟩ := HBI P hP δ ⟨hδ, hδsmall⟩
  obtain ⟨aR, haR, HAR⟩ := HBR P hP
  obtain ⟨aW, haW, HAW⟩ := HW h
    ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ q D P hq hD hP
    (η / E) (div_pos hη hE)
  refine ⟨min aI (min aR aW), lt_min haI (lt_min haR haW), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y Z κ
  obtain ⟨HY, hk8, _, hkhi, hm, hu, hv, hw, _, Hd0, Hdwall⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, _, HK, _, _, Hlo, _⟩ :=
    HAR a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, Hsmall⟩ :=
    HAW a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ ε ζ ν hε hζ hν ρ hρ
  let k := coreRadius (Y ρ 0) (Y ρ 2)
  let L := 1 + |Real.log a|
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [abs_nonneg (Real.log a)]
  have hL0 : 0 ≤ L := by linarith only [hL]
  change 8 ≤ k at hk8
  change k ≤ 64 / a at hkhi
  change 1 / (36864 * a ^ 2) ≤ -deriv κ ρ at Hlo
  change L * Real.sqrt (Y ρ 1 + Y ρ 3) ≤ η / E at Hsmall
  have hk0 : 0 < k := by linarith only [hk8]
  have hk' : 7 / 4 ≤ coreRadius (Y ρ 0) (Y ρ 2) := by change 7 / 4 ≤ k; linarith only [hk8]
  have Hd0' : |deriv (fun r => Y r 0) ρ| ≤ (B * L) * k ^ 2 := Hd0.trans (by
    have H := mul_le_mul_of_nonneg_left hL (mul_nonneg hB.le (sq_nonneg k))
    nlinarith only [H])
  obtain ⟨HZ, hU, hW, HU, HW⟩ := HC Y ρ (B * L) HY (mul_nonneg hB.le hL0)
    hk' hm.le hu hv hw Hd0' (fun i hi => by simpa only [mul_assoc] using Hdwall i hi)
  change |deriv (fun r => Z r 1) ρ| ≤ C * (B * L) * k ^ 2 * Real.sqrt (Y ρ 1 * Y ρ 2) * Real.sqrt (Z ρ 1) at HU
  change |deriv (fun r => Z r 3) ρ| ≤ C * (B * L) * k * Real.sqrt (Y ρ 3 * Y ρ 2) * Real.sqrt (Z ρ 3) at HW
  have Hratio : k ^ 2 ≤ 150994944 * |deriv κ ρ| := by
    calc
      _ ≤ (64 / a) ^ 2 := pow_le_pow_left₀ hk0.le hkhi 2
      _ = 150994944 * (1 / (36864 * a ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Hlo.trans (neg_le_abs _)) (by norm_num)
  have Hwall {x dx w : ℝ} (hw0 : 0 ≤ w) (hwle : w ≤ Y ρ 1 + Y ρ 3)
      (H : |dx| ≤ C * (B * L) * k ^ 2 * Real.sqrt (w * Y ρ 2) * Real.sqrt x) :
      |dx| ≤ η * Real.sqrt x * |deriv κ ρ| := by
    have Hroot := Real.sqrt_le_sqrt ((mul_le_of_le_one_right hw0 hv.2.le).trans hwle)
    calc
      _ ≤ C * (B * L) * k ^ 2 * Real.sqrt (Y ρ 1 + Y ρ 3) * Real.sqrt x := by
        exact H.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left Hroot (by positivity)) (Real.sqrt_nonneg x))
      _ ≤ C * (B * L) * (150994944 * |deriv κ ρ|) * Real.sqrt (Y ρ 1 + Y ρ 3) * Real.sqrt x := by gcongr
      _ = E * (L * Real.sqrt (Y ρ 1 + Y ρ 3)) * Real.sqrt x * |deriv κ ρ| := by dsimp only [E]; ring
      _ ≤ E * (η / E) * Real.sqrt x * |deriv κ ρ| := by gcongr
      _ = _ := by rw [mul_div_cancel₀ _ hE.ne']
  have HW' : |deriv (fun r => Z r 3) ρ| ≤ C * (B * L) * k ^ 2 * Real.sqrt (Y ρ 3 * Y ρ 2) * Real.sqrt (Z ρ 3) := by
    apply HW.trans
    gcongr
    nlinarith only [mul_le_mul_of_nonneg_left (show 1 ≤ k by linarith only [hk8]) hk0.le]
  exact ⟨HZ, HK, (by positivity [ha.1] : 0 < 1 / (36864 * a ^ 2)).trans_le Hlo, hU, hW,
    Hwall hu.1.le (le_add_of_nonneg_right hw.1.le) HU,
    Hwall hw.1.le (le_add_of_nonneg_left hu.1.le) HW'⟩

end BianchiIX
