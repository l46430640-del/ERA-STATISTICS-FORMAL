import BianchiIX.Dynamics.EraReturnOrbit
import BianchiIX.Dynamics.EraSelectedInputs

noncomputable section

namespace BianchiIX

open Set

/-- Every finite core-block time is locally C1 on the same phase-margin domains, uniformly in the number of cores. -/
theorem exists_era_time_regular :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β : ℝ) (X : CoreAngleState), 0 < β → β < 1 / 2 →
        (0 < X 1 ∧ X 1 ≤ ε / X 0) → (0 < X 2 ∧ X 2 ≤ ε / X 0) →
        X 1 + X 2 ≤ ε * (β / 2) ^ (2 * J) →
        ((m : ℝ) + 1 + β ≤ X 0 / 2 ∧ X 0 / 2 ≤ (m : ℝ) + 2 - β) →
        C * (X 1 + X 2) < β / 4 → ContDiffAt ℝ 1 (eraReturnTime η J m) X := by
  obtain ⟨δ, hδ, hδmax, HP⟩ := exists_era_bounded_phase_estimates
  obtain ⟨εK, hεK, _, K, hK, HK⟩ := exists_core_itinerary
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
  have hC : 1 ≤ C := hCP.trans (le_max_left _ _)
  refine ⟨ε, hε, C, hC, ?_⟩
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
  obtain ⟨Hall, Hconn, _, _, _⟩ := HK m β X hβ hβmax
    ⟨hu.1, hu.2.trans (hscale hεK')⟩ ⟨hw.1, hw.2.trans (hscale hεK')⟩ hphase
    ((hbound (le_max_right _ _)).trans (by linarith only [hβ]))
  obtain ⟨_, _, Hterminal, _⟩ := Hp m β X hβ hβmax
    ⟨hu.1, hu.2.trans (hscale hεP')⟩ ⟨hw.1, hw.2.trans (hscale hεP')⟩
    (hsmall.trans (mul_le_mul_of_nonneg_right hεP' (pow_nonneg (half_pos hβ).le _)))
    hphase (hbound (le_max_left _ _))
  have hbX : b * X 0 ≤ 2 * ε := by
    have hU := (le_div_iff₀ hX0).mp hu.2
    have hW := (le_div_iff₀ hX0).mp hw.2
    dsimp only [b]
    nlinarith only [hU, hW]
  have Hreflection (j : ℕ) (hj : j < m) :
      ContDiffAt ℝ 1 (coreReflectionTime ∘ G^[j]) X := by
    obtain ⟨_, _, _, HF, HT, Hz, Hsum, Herr, _⟩ := Hall j hj.le
    let Z := F (G^[j] X)
    have hZ4 : 31 / 8 ≤ Z 0 := by linarith only [(Hconn j hj).1, hβ]
    have hZ0 : 0 < Z 0 := lt_of_lt_of_le (by norm_num) hZ4
    have hZupper : Z 0 ≤ 2 * X 0 := by
      have he : |Z 0 - (X 0 - 2 * j)| < β / 4 :=
        ((le_add_of_nonneg_left (abs_nonneg _)).trans Herr).trans_lt (hbound (le_max_right _ _))
      nlinarith only [(abs_lt.mp he).2, hβmax, hX, Nat.cast_nonneg (α := ℝ) j]
    have hsmallZ (i : Fin 2) : 0 < Z i.succ ∧ Z i.succ ≤ εR / Z 0 := by
      have hZi := Hz i
      have hZb : Z i.succ ≤ b := by
        fin_cases i
        · exact (le_add_of_nonneg_right (Hz 1).le).trans Hsum
        · exact (le_add_of_nonneg_left (Hz 0).le).trans Hsum
      refine ⟨hZi, (le_div_iff₀ hZ0).mpr ?_⟩
      calc
        _ ≤ b * Z 0 := mul_le_mul_of_nonneg_right hZb hZ0.le
        _ ≤ b * (2 * X 0) := mul_le_mul_of_nonneg_left hZupper hb.le
        _ ≤ εR := by nlinarith only [hbX, hεR']
    obtain ⟨_, _, Hτ, _⟩ := HR Z hZ4 (hsmallZ 0) (hsmallZ 1)
    change ContDiffAt ℝ 1 (fun Y => reflectionReturnTime (F (G^[j] Y)) + coreRadiusReturnTime (G^[j] Y)) X
    exact ((Hτ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp X HF).add HT
  have Hprefix : ContDiffAt ℝ 1 (corePrefixTime m) X := by
    apply ContDiffAt.sum
    intro j hj
    exact Hreflection j (Finset.mem_range.mp hj)
  exact Hterminal.add ((Hall m le_rfl).2.2.2.2.1.add Hprefix)

/-- A single small budget cap gives local regularity of every retained original return time. -/
theorem exists_era_input_time_regular :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bcap m, ContDiffAt ℝ 1 (eraReturnTime η J m) p.2 := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_time_regular
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
