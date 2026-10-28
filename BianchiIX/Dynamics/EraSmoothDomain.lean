import BianchiIX.Dynamics.EraSmoothness

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology ContDiff

/-- An open phase-margin domain for a fixed finite physical itinerary. -/
def eraPhaseInterior (ε C : ℝ) (J m : ℕ) (β : ℝ) : Set CoreAngleState :=
  {X | 0 < X 1 ∧ 0 < X 2 ∧ X 1 * X 0 < ε ∧ X 2 * X 0 < ε ∧
    X 1 + X 2 < ε * (β / 2) ^ (2 * J) ∧
    (m : ℝ) + 1 + β < X 0 / 2 ∧ X 0 / 2 < (m : ℝ) + 2 - β ∧
    C * (X 1 + X 2) < β / 4}

theorem isOpen_eraPhaseInterior (ε C : ℝ) (J m : ℕ) (β : ℝ) :
    IsOpen (eraPhaseInterior ε C J m β) :=
  (isOpen_lt continuous_const (continuous_apply 1)).inter
    ((isOpen_lt continuous_const (continuous_apply 2)).inter
      ((isOpen_lt ((continuous_apply 1).mul (continuous_apply 0)) continuous_const).inter
        ((isOpen_lt ((continuous_apply 2).mul (continuous_apply 0)) continuous_const).inter
          ((isOpen_lt ((continuous_apply 1).add (continuous_apply 2)) continuous_const).inter
            ((isOpen_lt continuous_const ((continuous_apply 0).div_const 2)).inter
              ((isOpen_lt ((continuous_apply 0).div_const 2) continuous_const).inter
                (isOpen_lt (continuous_const.mul ((continuous_apply 1).add (continuous_apply 2)))
                  continuous_const)))))))

/-- Uniform passage estimates give smooth actual era maps on open domains for every finite core count. -/
theorem exists_era_smooth_interior :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ∃ C ≥ (1 : ℝ),
        ∀ (m : ℕ) (β : ℝ), 0 < β → β < 1 / 2 →
          ∀ X ∈ eraPhaseInterior ε C J m β,
            EraEventItinerary η J m X ∧
              ContDiffAt ℝ ∞ (eraReturnTime η J m) X ∧
              ContDiffAt ℝ ∞ (eraOutputState η J m) X ∧
              ContDiffAt ℝ ∞ (eraNextState η J m) X := by
  obtain ⟨δe, hδe, hδmax, HE⟩ := exists_era_event_itinerary
  obtain ⟨δt, hδt, _, HT⟩ := exists_era_time_regular
  refine ⟨min δe δt, lt_min hδe hδt, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨εe, hεe, Ce, hCe, He⟩ := HE η hη (hηδ.trans (min_le_left _ _)) J hJ
  obtain ⟨εt, hεt, Ct, hCt, Ht⟩ := HT η hη (hηδ.trans (min_le_right _ _)) J hJ
  let ε := min εe εt
  let C := max Ce Ct
  refine ⟨ε, lt_min hεe hεt, C, hCe.trans (le_max_left _ _), ?_⟩
  intro m β hβ hβmax
  have Hboth (Y : CoreAngleState) (hY : Y ∈ eraPhaseInterior ε C J m β) :
      EraEventItinerary η J m Y ∧ ContinuousAt (eraReturnTime η J m) Y := by
    obtain ⟨hu, hw, huε, hwε, hb, hlo, hhi, hmargin⟩ := hY
    have hY0 : 0 < Y 0 := by nlinarith only [hlo, hβ, Nat.cast_nonneg (α := ℝ) m]
    have hwall {z e : ℝ} (hz : z * Y 0 < ε) (he : ε ≤ e) : z ≤ e / Y 0 :=
      (le_div_iff₀ hY0).mpr (hz.le.trans he)
    have hsmall {e : ℝ} (he : ε ≤ e) : Y 1 + Y 2 ≤ e * (β / 2) ^ (2 * J) :=
      hb.le.trans (mul_le_mul_of_nonneg_right he (pow_nonneg (half_pos hβ).le _))
    have hbound {c : ℝ} (hc : c ≤ C) : c * (Y 1 + Y 2) < β / 4 :=
      (mul_le_mul_of_nonneg_right hc (add_pos hu hw).le).trans_lt hmargin
    exact ⟨He m β Y hβ hβmax
      ⟨hu, hwall huε (min_le_left _ _)⟩ ⟨hw, hwall hwε (min_le_left _ _)⟩
      (hsmall (min_le_left _ _)) ⟨hlo.le, hhi.le⟩ (hbound (le_max_left _ _)),
      (Ht m β Y hβ hβmax
        ⟨hu, hwall huε (min_le_right _ _)⟩ ⟨hw, hwall hwε (min_le_right _ _)⟩
        (hsmall (min_le_right _ _)) ⟨hlo.le, hhi.le⟩ (hbound (le_max_right _ _))).continuousAt⟩
  intro X hX
  have hnear : ∀ᶠ Y in 𝓝 X, Y ∈ eraPhaseInterior ε C J m β :=
    (isOpen_eraPhaseInterior ε C J m β).mem_nhds hX
  exact ⟨(Hboth X hX).1, eraReturn_contDiff_smooth (Hboth X hX).2
    (hnear.mono fun Y hY => (Hboth Y hY).1)⟩

/-- All retained inputs, including their closed phase endpoints, lie inside smooth physical branches. -/
theorem exists_era_input_smooth :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bcap m,
            ∃ U : Set CoreAngleState, IsOpen U ∧ p.2 ∈ U ∧
              (∀ X ∈ U, EraEventItinerary η J m X) ∧
              ContDiffOn ℝ ∞ (eraReturnTime η J m) U ∧
              ContDiffOn ℝ ∞ (eraOutputState η J m) U ∧
              ContDiffOn ℝ ∞ (eraNextState η J m) U := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_smooth_interior
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, C, hC, HE⟩ := Hδ η hη hηδ J (by omega)
  let a := ε * (1 / 2 : ℝ) ^ (2 * J) / 2
  have ha : 0 < a := by positivity
  have haε : a < ε := by
    have hpow : (1 / 2 : ℝ) ^ (2 * J) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp only [a]
    nlinarith only [hε, mul_le_mul_of_nonneg_left hpow hε.le]
  obtain ⟨Bstar, hBstar, hBone, HB⟩ := exists_retained_era_parameter_budget ha
    (show 0 ≤ 2 * C by linarith only [hC]) hσ hσone hσJ
  refine ⟨Bstar, hBstar, hBone, ?_⟩
  intro Bcap hcap m p hp
  obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := HB p.1 ⟨hB.1, hB.2.trans hcap⟩
  have hm' : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have hrpos : 0 < p.2 0 := by nlinarith only [hr.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hBr : p.1 * p.2 0 ≤ a :=
    (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hm')
  have hwall {z : ℝ} (hz : z ≤ p.1) : z * p.2 0 < ε :=
    ((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBr).trans_lt haε
  have hpower : a * (p.1 ^ σ / 2) ^ (2 * J) =
      ε * ((p.1 ^ σ / 2) / 2) ^ (2 * J) / 2 := by
    dsimp only [a]
    rw [show (p.1 ^ σ / 2) / 2 = (1 / 2) * (p.1 ^ σ / 2) by ring, mul_pow]
    ring
  have hsmall' : p.2 1 + p.2 2 < ε * ((p.1 ^ σ / 2) / 2) ^ (2 * J) := by
    have hpos : 0 < ε * ((p.1 ^ σ / 2) / 2) ^ (2 * J) := by positivity
    rw [hpower] at hsmall
    exact (hsum.trans hsmall).trans_lt (by linarith only [hpos])
  have hmargin' : C * (p.2 1 + p.2 2) < (p.1 ^ σ / 2) / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ C by linarith only [hC])
    nlinarith only [hmargin, hmul]
  let U := eraPhaseInterior ε C J m (p.1 ^ σ / 2)
  have hpU : p.2 ∈ U := ⟨hu, hw, hwall (by linarith only [hsum, hw]),
    hwall (by linarith only [hsum, hu]), hsmall', by linarith only [hr.1, hβ],
    by linarith only [hr.2, hβ], hmargin'⟩
  have H (X : CoreAngleState) (hX : X ∈ U) :=
    HE m (p.1 ^ σ / 2) (half_pos hβ) (by linarith only [hβmax]) X hX
  exact ⟨U, isOpen_eraPhaseInterior _ _ _ _ _, hpU, fun X hX => (H X hX).1,
    fun X hX => (H X hX).2.1.contDiffWithinAt,
    fun X hX => (H X hX).2.2.1.contDiffWithinAt,
    fun X hX => (H X hX).2.2.2.contDiffWithinAt⟩

end BianchiIX
