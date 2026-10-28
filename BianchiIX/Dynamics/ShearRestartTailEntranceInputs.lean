import BianchiIX.Dynamics.ShearRestartTailProjective
import BianchiIX.Dynamics.ShearTailCoreRadius
import BianchiIX.Analysis.ShearTailEntranceScale

noncomputable section

namespace BianchiIX

open Set

def restartShearTailProjectiveEntry (h a q ζ ν t ρ : ℝ) : ProjectiveState :=
  toProjectiveState (restartShearTailFlow h a q ζ ν t ρ)

/-- The exact tail supplies all entrance data, with the logarithmic loss retained only in wall responses. -/
theorem exists_restartShearTail_entrance_inputs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ B > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∀ δ ∈ Ioc (0 : ℝ) (1 / 10000),
          ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Y := restartShearTailProjectiveEntry h a q ζ ν (shearTailTime a D)
            let k := coreRadius (Y ρ 0) (Y ρ 2)
            let L := 1 + |Real.log a|
            DifferentiableAt ℝ Y ρ ∧ 8 ≤ k ∧ 1 / (24 * a) ≤ k ∧ k ≤ 64 / a ∧
            1 < Y ρ 0 ∧ (0 < Y ρ 1 ∧ Y ρ 1 ≤ δ) ∧ (0 < Y ρ 2 ∧ Y ρ 2 < 1) ∧
            (0 < Y ρ 3 ∧ Y ρ 3 ≤ δ) ∧ L * (Y ρ 1 + Y ρ 3) ≤ 1 ∧
            |deriv (fun r => Y r 0) ρ| ≤ B * k ^ 2 ∧
            ∀ i : Fin 4, i ≠ 0 → |deriv (fun r => Y r i) ρ| ≤ B * L * k * Y ρ i := by
  obtain ⟨CR, hCR, hR, hhR, HR⟩ := exists_restartShearTail_radial_control
  obtain ⟨CP, hCP, hP, hhP, HP⟩ := exists_restartShearTail_projective_control
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨min hR (min hP hV), lt_min hhR (lt_min hhP hhV), ?_⟩
  intro h hh q D hq hD
  have hCR0 : 0 ≤ CR := by linarith only [hCR]
  have hCP0 : 0 ≤ CP := by linarith only [hCP]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hD0 : 0 ≤ D := by linarith only [hD]
  let M := 1000 + 2400 * (13 + 20 * CP * q + D)
  let N := 3 + 4 * CR * q + D
  let B := 60000 * M * N
  have hM : 0 < M := by dsimp only [M]; positivity
  have hN : 1 ≤ N := by dsimp only [N]; nlinarith only [mul_nonneg hCR0 hq0, hD0]
  have hN0 : 0 < N := by linarith only [hN]
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro P hPexp δ hδ
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD0 hPexp
  obtain ⟨aP, haP, HAP⟩ := HP h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q D P hq hD0 hPexp
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩ q D P hq hD0 hPexp
  obtain ⟨aS, haS, HAS⟩ := exists_shearTail_entrance_wall_scale (h := h) hq hD hδ.1
  refine ⟨min aR (min aP (min aV aS)), lt_min haR (lt_min haP (lt_min haV haS)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Y k L
  let T := shearTailTime a D
  let z := restartShearTailFlow h a q ζ ν T ρ
  let v := restartShearTailRadialVariation h a q ζ ν T ρ
  let L₀ := shearTailLogSize (restartShearTailFlow h a q ζ ν 0 ρ)
    (restartShearTailRadialVariation h a q ζ ν 0 ρ)
  let w := shearTailProjectiveLogVariation z v
  obtain ⟨hasmall, hT, HL₀, _, _, _, _, _, HRT⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, HPT⟩ := HAP a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, _, _, _, _, HVT, Hpowers⟩ :=
    HAV a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
      ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  obtain ⟨ha1, Hsmall⟩ := HAS a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨HD, Hpos, _, _, _⟩ := HRT T ⟨hT, le_rfl⟩
  obtain ⟨_, _, HDlog, _, HWlog, HMder⟩ := HPT T ⟨hT, le_rfl⟩
  obtain ⟨_, _, Hcon, Hnon, Hreg, _, _, _, _, HAl, _, HVlt⟩ := HVT T ⟨hT, le_rfl⟩
  have hA : 0 < 1 + z 0 := (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le HAl
  have HY : DifferentiableAt ℝ Y ρ :=
    ((contDiffAt_toProjectiveState 1 hA.ne').differentiableAt (by norm_num)).comp ρ HD.differentiableAt
  obtain ⟨hm, hk8, hklo, hkhi⟩ := shearTail_core_radius_bounds ⟨ha.1, hasmall⟩ Hcon Hreg Hnon HVlt
  change 8 ≤ k at hk8
  change 1 / (24 * a) ≤ k at hklo
  change k ≤ 64 / a at hkhi
  have HPpos := toProjectiveState_positive hA Hpos
  change 0 < Y ρ 1 ∧ 0 < Y ρ 2 ∧ 0 < Y ρ 3 at HPpos
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [abs_nonneg (Real.log a)]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have Hwall : Y ρ 1 + Y ρ 3 ≤ 20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1) := by
    have hε1 : ε ≤ 1 := by linarith only [hε.2]
    have Hε := mul_le_mul_of_nonneg_right hε1 (by positivity [ha.1] : 0 ≤ 80 * a ^ (D / 2 - 1))
    have Hn : Y ρ 1 ≤ 20 * h * a ^ (q - 2) := Hpowers.1
    have Hy : Y ρ 3 ≤ 80 * ε * a ^ (D / 2 - 1) := Hpowers.2.2
    nlinarith only [Hn, Hy, Hε]
  have HLwall : L * (Y ρ 1 + Y ρ 3) ≤ δ := by
    have H := mul_le_mul_of_nonneg_right Hwall hL0
    change (20 * h * a ^ (q - 2) + 80 * a ^ (D / 2 - 1)) * L ≤ δ at Hsmall
    nlinarith only [H, Hsmall]
  have Hsum : Y ρ 1 + Y ρ 3 ≤ δ := by
    have H := mul_le_mul_of_nonneg_right hL (add_nonneg HPpos.1.le HPpos.2.2.le)
    linarith only [H, HLwall]
  have htime : a * T = D * |Real.log a| := by
    dsimp only [T, shearTailTime]
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) ha.1.ne', Real.log_one, zero_sub,
      abs_of_nonpos (Real.log_nonpos ha.1.le ha1)]
    field_simp [ha.1.ne']
  have Hbudget : 1 / a + L₀ + T ≤ N * L / a := by
    apply (le_div_iff₀ ha.1).mpr
    have H := mul_le_mul_of_nonneg_left HL₀ ha.1.le
    have HC := mul_le_mul_of_nonneg_right ha1 (by positivity : 0 ≤ 4 * CR * q * |Real.log a|)
    have HI : (1 / a) * a = 1 := by field_simp [ha.1.ne']
    dsimp only [N, L]
    nlinarith only [H, HC, HI, htime, ha1, mul_nonneg hCR0 hq0, hD0, abs_nonneg (Real.log a)]
  have HW : |w 2| + |w 3| + |w 4| ≤ M * N * L / a := HWlog.trans
    ((mul_le_mul_of_nonneg_left Hbudget hM.le).trans_eq (by ring))
  have hki : 1 / a ≤ 24 * k := by
    calc
      _ = 24 * (1 / (24 * a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hklo (by norm_num)
  have hBshear : 34560 * M ≤ B := by
    dsimp only [B]
    nlinarith only [mul_le_mul_of_nonneg_left hN hM.le, hM]
  have Hdm : |deriv (fun r => Y r 0) ρ| ≤ B * k ^ 2 := HMder.trans (by
    calc
      _ = 60 * M * (1 / a) ^ 2 := by ring
      _ ≤ 60 * M * (24 * k) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity [ha.1]) hki 2) (by positivity)
      _ = 34560 * M * k ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBshear (sq_nonneg k))
  have Hlog (i : Fin 4) : HasDerivAt (fun r => Real.log (Y r i)) (w i.succ) ρ := by
    fin_cases i
    · exact hasDerivAt_pi.mp HDlog 1
    · exact hasDerivAt_pi.mp HDlog 2
    · exact hasDerivAt_pi.mp HDlog 3
    · exact hasDerivAt_pi.mp HDlog 4
  have HwallDer (i : Fin 4) (hi : i ≠ 0) :
      |deriv (fun r => Y r i) ρ| ≤ B * L * k * Y ρ i := by
    have hy : 0 < Y ρ i := by
      fin_cases i
      · exact (hi rfl).elim
      · exact HPpos.1
      · exact HPpos.2.1
      · exact HPpos.2.2
    have hw : |w i.succ| ≤ M * N * L / a := by
      fin_cases i
      · exact (hi rfl).elim
      · change |w 2| ≤ _
        linarith only [HW, abs_nonneg (w 3), abs_nonneg (w 4)]
      · change |w 3| ≤ _
        linarith only [HW, abs_nonneg (w 2), abs_nonneg (w 4)]
      · change |w 4| ≤ _
        linarith only [HW, abs_nonneg (w 2), abs_nonneg (w 3)]
    have Hlog' := ((differentiableAt_pi.mp HY i).hasDerivAt).log hy.ne'
    have Heq := Hlog'.unique (Hlog i)
    have Habs : |deriv (fun r => Y r i) ρ| ≤ Y ρ i * (M * N * L / a) := by
      rw [← Heq, abs_div, abs_of_pos hy] at hw
      simpa only [mul_comm] using (div_le_iff₀ hy).mp hw
    have HBwall : 24 * M * N ≤ B := by dsimp only [B]; nlinarith only [mul_pos hM hN0]
    calc
      _ ≤ Y ρ i * (M * N * L / a) := Habs
      _ ≤ Y ρ i * (M * N * L * (24 * k)) := by
        rw [div_eq_mul_inv, show a⁻¹ = 1 / a by ring]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hki (by positivity)) hy.le
      _ = (24 * M * N) * L * k * Y ρ i := by ring
      _ ≤ _ := by
        have hk0 : 0 ≤ k := by linarith only [hk8]
        nlinarith only [mul_le_mul_of_nonneg_right HBwall (by positivity : 0 ≤ L * k * Y ρ i)]
  exact ⟨HY, hk8, hklo, hkhi, hm,
    ⟨HPpos.1, by linarith only [Hsum, HPpos.2.2]⟩, ⟨HPpos.2.1, HVlt⟩,
    ⟨HPpos.2.2, by linarith only [Hsum, HPpos.1]⟩,
    HLwall.trans (hδ.2.trans (by norm_num)), Hdm, HwallDer⟩

end BianchiIX
