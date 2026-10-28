import BianchiIX.Dynamics.TerminalNaturalCone
import BianchiIX.Analysis.PositiveLogDistortion

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def terminalNaturalTime (η : ℝ) (J : ℕ) (Y : ExitTailState) : ℝ :=
  terminalConnectionTime (η * ((Y 0 - 2) / 2) ^ J) Y

def terminalNaturalBoundedPhase (η : ℝ) (J : ℕ) (Y : ExitTailState) : ℝ :=
  2 / terminalNaturalPhase η J Y

/-- The bounded phase uses the same three-column cone estimate after a scalar change of scale. -/
theorem terminal_bounded_phase_cone_direction (L : ExitTailState →L[ℝ] ℝ) (d : ExitTailState)
    {C b u w : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hsum : u + w ≤ b)
    (hd0 : d 0 = 1) (hd1 : |d 1| ≤ Real.sqrt u) (hd2 : |d 2| ≤ Real.sqrt w)
    (hrad : |L (Pi.single 0 1) - 1 / 2| ≤ C * b)
    (hwall : |L (Pi.single 1 1)| + |L (Pi.single 2 1)| ≤ C) :
    |2 * L d - 1| ≤ 4 * C * Real.sqrt b := by
  have hr : |(-2 : ℝ) * L (Pi.single 0 1) + 1| ≤ 2 * C * b := by
    rw [show -2 * L (Pi.single 0 1) + 1 = -(2 * (L (Pi.single 0 1) - 1 / 2)) by ring,
      abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left hrad (by norm_num)).trans_eq (by ring)
  have hw' : |(-2 : ℝ) * L (Pi.single 1 1)| + |(-2 : ℝ) * L (Pi.single 2 1)| ≤ 2 * C := by
    simpa only [abs_mul, show |(-2 : ℝ)| = 2 by norm_num, ← mul_add] using
      mul_le_mul_of_nonneg_left hwall (by norm_num : (0 : ℝ) ≤ 2)
  have H := terminal_phase_cone_direction ((-2 : ℝ) • L) d (α := 1) (C := 2 * C)
    (by norm_num) (by positivity) hb (by simpa using hb1) hu hw hsum hd0 hd1 hd2
    (by simpa using hr) (by simpa using hw')
  simpa only [smul_apply, smul_eq_mul, one_pow, one_mul,
    show -2 * L d + 1 = -(2 * L d - 1) by ring, abs_neg,
    show 2 * (2 * C) = 4 * C by ring] using H

/-- Natural-height bounded phase estimates and its first physical arrival hold on one common domain. -/
theorem exists_terminalNatural_bounded_phase_estimates :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let x := axisCycle (fromProjectiveState (coreTailEntry Y))
      let Q := terminalNaturalBoundedPhase η J
      let T := terminalNaturalTime η J Y
      ContDiffAt ℝ 2 Q Y ∧ ContDiffAt ℝ 2 (terminalNaturalTime η J) Y ∧
      ContDiffAt ℝ 2 (terminalNaturalState η J) Y ∧
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
        projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
      toProjectiveState (normalizedMaxCurve x 0 T) = terminalNaturalState η J Y ∧
      terminalNaturalState η J Y 2 = 1 ∧
      0 < normalizedEventRate projectiveActiveWall x 0 T ∧
      |Q Y - α| ≤ C * b ∧
      ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt u → |d 2| ≤ Real.sqrt w →
        1 / 4 ≤ fderiv ℝ Q Y d ∧ |2 * fderiv ℝ Q Y d - 1| ≤ C * Real.sqrt b ∧
          |Real.log (2 * fderiv ℝ Q Y d)| ≤ C * Real.sqrt b := by
  obtain ⟨δ, hδ, hδmax, HE⟩ := exists_terminal_bounded_phase_statistics
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨A, hA, εp, hεp, HP⟩ := HE η ⟨hη, hηδ⟩ J hJ
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hη100 : η ≤ 1 / 100 := (hηδ.trans hδmax).trans (by norm_num)
  have hηin : η ≤ (1 / 10000 : ℝ) / (4 * (11 / 5) ^ (0 : ℕ)) := by
    norm_num
    exact hηδ.trans hδmax
  obtain ⟨εh, hεh, HH⟩ := exists_terminal_connection_height_freezing
    (εin := 1 / 10000) (η := η) (q := 0) (J := J) (by norm_num)
    ⟨hη, hη100⟩ (by omega) hηin
  obtain ⟨εa, hεa, HA⟩ := exists_terminal_connection_first_arrival
    (εin := 1 / 10000) (η := η) (q := 0) (J := J) (by norm_num)
    ⟨hη, hη100⟩ (by omega) hηin
  let r := 1 / (16 * A)
  have hr : 0 < r := by dsimp [r]; positivity
  let ε := min εp (min εh (min εa (min 1 (r ^ 2))))
  have hε : 0 < ε := lt_min hεp (lt_min hεh (lt_min hεa (lt_min (by norm_num) (sq_pos_of_pos hr))))
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεr : ε ≤ r ^ 2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨8 * A, by linarith only [hA], ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y x Q T
  have hs {e : ℝ} (he : ε ≤ e) : b ≤ e * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right he (pow_nonneg hα.1.le _))
  obtain ⟨_, HQ, Hvalue, Hwall⟩ := HP η α b u w le_rfl hηδ hα hb
    (hs (min_le_left _ _)) hsum hu hw
  obtain ⟨_, _, Hfreeze⟩ := HH α b u w hα hb (hs ((min_le_right _ _).trans (min_le_left _ _))) hsum hu hw
  obtain ⟨_, _, _, _, _, Hfirst, _, _, Hactual, Hactive, Htrans, _, _⟩ :=
    HA α b u w hα hb (hs ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) hsum hu hw
  let a := fun Z : ExitTailState => η * ((Z 0 - 2) / 2) ^ J
  have ha : ContinuousAt a Y :=
    ((((continuousAt_apply 0 Y).sub_const 2).div_const 2).pow J).const_mul η
  have haY : a Y = η * α ^ J := by dsimp only [a, Y]; simp only [Matrix.cons_val_zero]; congr 1; congr 1; ring
  obtain ⟨Hnear, HT, HS⟩ := Hfreeze a ha haY
  have Hphase : Q =ᶠ[𝓝 Y] terminalBoundedPhase (η * α ^ J) := by
    filter_upwards [Hnear] with Z hZ
    change 2 / coreRadius (terminalConnectionState (a Z) Z 0) (terminalConnectionState (a Z) Z 2) = _
    rw [hZ.2]
    rfl
  have htime : T = terminalConnectionTime (η * α ^ J) Y := by
    change terminalConnectionTime (a Y) Y = _
    rw [haY]
  have hstate : terminalNaturalState η J Y = terminalConnectionState (η * α ^ J) Y := by
    change terminalConnectionState (a Y) Y = _
    rw [haY]
  have hbε : b ≤ ε := hsmall.trans (mul_le_of_le_one_right hε.le (pow_le_one₀ hα.1.le hα.2))
  have hb1 := hbε.trans hε1
  have hroot : Real.sqrt b ≤ r := Real.sqrt_le_iff.mpr ⟨hr.le, hbε.trans hεr⟩
  have hquarter : 4 * A * Real.sqrt b ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left hroot (by positivity)).trans_eq (by dsimp [r]; field_simp; norm_num)
  refine ⟨HQ.congr_of_eventuallyEq Hphase, HT, HS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [htime]
  · rwa [htime, hstate]
  · rwa [hstate]
  · rwa [htime]
  · rw [Hphase.self_of_nhds]
    exact ((le_add_of_nonneg_right (abs_nonneg _)).trans Hvalue).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hA] : A ≤ 8 * A) hb.le)
  · intro d hd0 hd1 hd2
    have Hd := terminal_bounded_phase_cone_direction (fderiv ℝ (terminalBoundedPhase (η * α ^ J)) Y) d
      hA0.le hb.le hb1 hu.le hw.le (by simpa only [abs_of_pos hu, abs_of_pos hw] using hsum)
      hd0 hd1 hd2 ((le_add_of_nonneg_left (abs_nonneg _)).trans Hvalue) Hwall
    rw [← Hphase.fderiv_eq] at Hd
    have hmargin : 1 / 2 ≤ 2 * fderiv ℝ Q Y d := by
      linarith only [(abs_le.mp (Hd.trans hquarter)).1]
    refine ⟨by linarith only [hmargin], Hd.trans ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_right (by linarith only [hA] : 4 * A ≤ 8 * A) (Real.sqrt_nonneg _)
    · exact (abs_log_le_twice_sub_one_of_half_le hmargin).trans
        ((mul_le_mul_of_nonneg_left Hd (by norm_num)).trans_eq (by ring))

end BianchiIX
