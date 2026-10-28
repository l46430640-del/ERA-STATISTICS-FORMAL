import BianchiIX.Dynamics.CoreEventSections
import BianchiIX.Dynamics.EraReturnOrbit
import BianchiIX.Dynamics.EraSelectedInputs

noncomputable section

namespace BianchiIX

open Set

/-- A finite block of actual first core returns, followed by its first terminal connection. -/
structure EraEventItinerary (η : ℝ) (J m : ℕ) (X : CoreAngleState) : Prop where
  core : ∀ j ≤ m,
    let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
    2 < Y 0 ∧
      (projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) = 1 ∧
        0 < normalizedEventRate projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) 0 0) ∧
      coreRadiusReturnValid Y ∧
      coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
        projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y)
  reflection : ∀ j < m,
    let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
    let Z := coreReturnState coreRadiusReturnTime Y
    let x := axisSwap (fromProjectiveState (coreTailEntry Z))
    4 < Z 0 ∧
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
        projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} (reflectionReturnTime Z) ∧
      toProjectiveState (normalizedMaxCurve x 0 (reflectionReturnTime Z)) =
        coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j + 1] X) ∧
      coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j + 1] X) =
        projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))
  terminal :
    let Z := eraCoreExit m X
    let x := axisCycle (fromProjectiveState (coreTailEntry Z))
    let T := terminalNaturalTime η J Z
    (2 < Z 0 ∧ Z 0 < 4) ∧
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
        projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
      toProjectiveState (normalizedMaxCurve x 0 T) = terminalNaturalState η J Z ∧
      terminalNaturalState η J Z 2 = 1 ∧
      0 < normalizedEventRate projectiveActiveWall x 0 T
  count : Nat.floor (X 0 / 2) = m + 1

theorem EraEventItinerary.first_terminal {η : ℝ} {J m : ℕ} {X : CoreAngleState}
    (H : EraEventItinerary η J m X) :
    IsLeast {j : ℕ | 2 < eraCoreExit j X 0 ∧ eraCoreExit j X 0 < 4} m := by
  refine ⟨H.terminal.1, ?_⟩
  intro j hj
  by_contra! hlt
  have hR := (H.reflection j hlt).1
  exact (not_lt_of_ge hR.le) hj.2

/-- The phase-margin estimates certify every event in the block, including first arrivals in the new axis chart. -/
theorem exists_era_event_itinerary :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β : ℝ) (X : CoreAngleState), 0 < β → β < 1 / 2 →
        (0 < X 1 ∧ X 1 ≤ ε / X 0) → (0 < X 2 ∧ X 2 ≤ ε / X 0) →
        X 1 + X 2 ≤ ε * (β / 2) ^ (2 * J) →
        ((m : ℝ) + 1 + β ≤ X 0 / 2 ∧ X 0 / 2 ≤ (m : ℝ) + 2 - β) →
        C * (X 1 + X 2) < β / 4 → EraEventItinerary η J m X := by
  obtain ⟨δ, hδ, hδmax, HP⟩ := exists_era_bounded_phase_estimates
  obtain ⟨εK, hεK, hεKmax, K, hK, HK⟩ := exists_core_itinerary
  obtain ⟨εR, hεR, _, _, _, HR⟩ := exists_reflectionReturn_phase_bounds
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨εP, hεP, _, CP, hCP, Hp⟩ := HP η hη hηδ J hJ
  let ε := min εP (min εK (εR / 4))
  let C := max CP K
  have hε : 0 < ε := lt_min hεP (lt_min hεK (div_pos hεR (by norm_num)))
  have hεP' : ε ≤ εP := min_le_left _ _
  have hεK' : ε ≤ εK := (min_le_right _ _).trans (min_le_left _ _)
  have hεR' : ε ≤ εR / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, C, hCP.trans (le_max_left _ _), ?_⟩
  intro m β X hβ hβmax hu hw hsmall hphase hmargin
  let F := coreReturnState coreRadiusReturnTime
  let G := coreReflectionState coreRadiusReturnTime
  let b := X 1 + X 2
  have hb : 0 < b := add_pos hu.1 hw.1
  have hX : 2 < X 0 := by nlinarith only [hphase.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hX0 : 0 < X 0 := lt_trans (by norm_num) hX
  have hscale {e : ℝ} (he : ε ≤ e) : ε / X 0 ≤ e / X 0 :=
    div_le_div_of_nonneg_right he hX0.le
  have hbound {c : ℝ} (hc : c ≤ C) : c * b < β / 4 :=
    (mul_le_mul_of_nonneg_right hc hb.le).trans_lt hmargin
  obtain ⟨Hall, Hconn, Hlast, _, _⟩ := HK m β X hβ hβmax
    ⟨hu.1, hu.2.trans (hscale hεK')⟩ ⟨hw.1, hw.2.trans (hscale hεK')⟩ hphase
    ((hbound (le_max_right _ _)).trans (by linarith only [hβ]))
  obtain ⟨_, _, _, _, _, _, hcount, _, _, _, hterminal, _, Hfirst, Hactual, Hunit, Hup, _⟩ :=
    Hp m β X hβ hβmax ⟨hu.1, hu.2.trans (hscale hεP')⟩ ⟨hw.1, hw.2.trans (hscale hεP')⟩
      (hsmall.trans (mul_le_mul_of_nonneg_right hεP' (pow_nonneg (half_pos hβ).le _)))
      hphase (hbound (le_max_left _ _))
  have hbX : b * X 0 ≤ 2 * ε := by
    dsimp only [b]
    nlinarith only [(le_div_iff₀ hX0).mp hu.2, (le_div_iff₀ hX0).mp hw.2]
  have hbquarter : b ≤ 1 / 4 :=
    (hsmall.trans (mul_le_of_le_one_right hε.le
      (pow_le_one₀ (half_pos hβ).le (by linarith only [hβmax])))).trans
      (hεK'.trans (hεKmax.trans (by norm_num)))
  have Hz (j : ℕ) (hj : j ≤ m) (i : Fin 2) :
      0 < F (G^[j] X) i.succ ∧ F (G^[j] X) i.succ ≤ b := by
    obtain ⟨_, _, _, _, _, Hpos, Hsum, _⟩ := Hall j hj
    refine ⟨Hpos i, ?_⟩
    fin_cases i
    · exact (le_add_of_nonneg_right (Hpos 1).le).trans Hsum
    · exact (le_add_of_nonneg_left (Hpos 0).le).trans Hsum
  have Hreflect (j : ℕ) (hj : j < m) := by
    let Z := F (G^[j] X)
    have hZ4 : 31 / 8 ≤ Z 0 := by linarith only [(Hconn j hj).1, hβ]
    have hZ0 : 0 < Z 0 := lt_of_lt_of_le (by norm_num) hZ4
    have hZupper : Z 0 ≤ 2 * X 0 := by
      have he : |Z 0 - (X 0 - 2 * j)| < β / 4 :=
        ((le_add_of_nonneg_left (abs_nonneg _)).trans (Hall j hj.le).2.2.2.2.2.2.2.1).trans_lt
          (hbound (le_max_right _ _))
      nlinarith only [(abs_lt.mp he).2, hβmax, hX, Nat.cast_nonneg (α := ℝ) j]
    have hsmallZ (i : Fin 2) : 0 < Z i.succ ∧ Z i.succ ≤ εR / Z 0 := by
      refine ⟨(Hz j hj.le i).1, (le_div_iff₀ hZ0).mpr ?_⟩
      calc
        _ ≤ b * Z 0 := mul_le_mul_of_nonneg_right (Hz j hj.le i).2 hZ0.le
        _ ≤ b * (2 * X 0) := mul_le_mul_of_nonneg_left hZupper hb.le
        _ ≤ εR := by nlinarith only [hbX, hεR']
    exact HR Z hZ4 (hsmallZ 0) (hsmallZ 1)
  have Hentry (j : ℕ) (hj : j ≤ m) (i : Fin 2) :
      0 ≤ (G^[j] X) i.succ ∧ (G^[j] X) i.succ ≤ 1 / 4 := by
    cases j with
    | zero =>
      fin_cases i
      · exact ⟨hu.1.le, (le_add_of_nonneg_right hw.1.le).trans hbquarter⟩
      · exact ⟨hw.1.le, (le_add_of_nonneg_left hu.1.le).trans hbquarter⟩
    | succ j =>
      have hjm : j < m := by omega
      have Hwall := (Hreflect j hjm).2.2.2.2.2.1 i
      rw [Function.iterate_succ_apply']
      exact ⟨Hwall.1.le, Hwall.2.trans ((Hz j hjm.le i).2.trans hbquarter)⟩
  refine ⟨?_, ?_, ⟨hterminal, Hfirst, Hactual, Hunit, Hup⟩, hcount⟩
  · intro j hj
    have hk : 2 < G^[j] X 0 := by linarith only [(Hall j hj).1, hβ]
    have hR : 2 ≤ F (G^[j] X) 0 := by
      rcases lt_or_eq_of_le hj with hlt | rfl
      · linarith only [(Hconn j hlt).1, hβ]
      · linarith only [Hlast.1, hβ]
    exact ⟨hk, coreRadiusEntry_upward hk.le (Hentry j hj 0) (Hentry j hj 1),
      (Hall j hj).2.1, coreRadiusReturn_exit_chart (Hall j hj).2.1 hR
        ⟨(Hz j hj 0).1.le, (Hz j hj 0).2.trans hbquarter⟩
        ⟨(Hz j hj 1).1.le, (Hz j hj 1).2.trans hbquarter⟩⟩
  · intro j hj
    obtain ⟨hf, ha, _⟩ := Hreflect j hj
    have hD := unit_active_wall_denom_pos (y := coreTailEntry (F (G^[j] X))) rfl
      ⟨(Hz j hj.le 0).1.le, (Hz j hj.le 0).2.trans hbquarter⟩
      ⟨(Hz j hj.le 1).1.le, (Hz j hj.le 1).2.trans hbquarter⟩
    obtain ⟨hfirst, hactual⟩ := reflectionReturn_first_active hD hf ha
    refine ⟨by linarith only [(Hconn j hj).1, hβ], hfirst, ?_, (Hconn j hj).2.2⟩
    simpa only [Function.iterate_succ_apply', F, G, coreReflectionState,
      coreConnectionParameters, reflectionReturnState] using hactual

/-- All retained inputs satisfy the actual event rules on one common budget cap. -/
theorem exists_era_input_event_itinerary :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bcap m, EraEventItinerary η J m p.2 := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_event_itinerary
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, C, hC, HE⟩ := Hδ η hη hηδ J (by omega)
  obtain ⟨Bstar, hBstar, hBone, HB⟩ := exists_retained_era_parameter_budget hε
    (le_trans zero_le_one hC) hσ hσone hσJ
  refine ⟨Bstar, hBstar, hBone, ?_⟩
  intro Bcap hcap m p hp
  obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := HB p.1 ⟨hB.1, hB.2.trans hcap⟩
  have hm' : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have hrpos : 0 < p.2 0 := by nlinarith only [hr.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hBr : p.1 * p.2 0 ≤ ε :=
    (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hm')
  have hwall {z : ℝ} (hz : z ≤ p.1) : z ≤ ε / p.2 0 :=
    (le_div_iff₀ hrpos).mpr ((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBr)
  exact HE m (p.1 ^ σ) p.2 hβ (by linarith only [hβmax])
    ⟨hu, hwall (by linarith only [hsum, hw])⟩ ⟨hw, hwall (by linarith only [hsum, hu])⟩
    (hsum.trans hsmall) ⟨by linarith only [hr.1], by linarith only [hr.2]⟩
    ((mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one hC)).trans_lt hmargin)

end BianchiIX
