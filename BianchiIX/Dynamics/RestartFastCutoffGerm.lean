import BianchiIX.Dynamics.RestartCutoffGerm
import BianchiIX.Dynamics.RestartAngularFastInterval

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Every bounded angular family has cutoff-independent ordinary return germs and derivative values. -/
theorem exists_restartAngular_fast_cutoff_germs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q₀ q₁ P : ℝ, 3 < q₀ → q₀ ≤ q₁ → 4 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ θ ζ : ℝ,
          |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ a ^ P) → ∀ ρ ∈ Icc a (2 * a),
          let s₀ := q₀ / 2 * Real.log (1 / a)
          let s₁ := q₁ / 2 * Real.log (1 / a)
          let base := ((θ, ζ), ρ)
          let F := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartReturnParameters h s v.1.1 v.1.2 v.2
          let G := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartReturnState h s v.1.1 v.1.2 v.2
          let X := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartReturnPhase h s v.1.1 v.1.2 v.2
          let T := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartReturnTime h s v.1.1 v.1.2 v.2
          F s₀ =ᶠ[𝓝 base] F s₁ ∧ G s₀ =ᶠ[𝓝 base] G s₁ ∧
          X s₀ =ᶠ[𝓝 base] X s₁ ∧ T s₀ =ᶠ[𝓝 base] T s₁ ∧
          ∀ n : ℕ, iteratedFDeriv ℝ n (F s₀) base = iteratedFDeriv ℝ n (F s₁) base ∧
            iteratedFDeriv ℝ n (G s₀) base = iteratedFDeriv ℝ n (G s₁) base ∧
            iteratedFDeriv ℝ n (X s₀) base = iteratedFDeriv ℝ n (X s₁) base ∧
            iteratedFDeriv ℝ n (T s₀) base = iteratedFDeriv ℝ n (T s₁) base := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartAngular_fast_interval
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_entry
  refine ⟨min hI hE, lt_min hhI hhE, ?_⟩
  intro h hh L hL q₀ q₁ P hq₀ hq hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    L hL q₀ q₁ (by linarith only [hq₀]) hq
  obtain ⟨a₀, ha₀, HE₀⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
    L hL q₀ P hq₀ hP (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨a₁, ha₁, HE₁⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
    L hL q₁ P (hq₀.trans_le hq) hP (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aI (min a₀ (min a₁ (1 / 2))),
    lt_min haI (lt_min ha₀ (lt_min ha₁ (by norm_num))), ?_⟩
  intro a ha θ ζ hθ hζ ρ hρ s₀ s₁ base F G X T
  have HGerms : F s₀ =ᶠ[𝓝 base] F s₁ ∧ G s₀ =ᶠ[𝓝 base] G s₁ ∧
      X s₀ =ᶠ[𝓝 base] X s₁ ∧ T s₀ =ᶠ[𝓝 base] T s₁ := by
    by_cases he : q₀ = q₁
    · have hs : s₀ = s₁ := by dsimp only [s₀, s₁]; rw [he]
      rw [hs]
      exact ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
    have ha0 := (ha.2.trans (min_le_right _ _)).trans (min_le_left _ _)
    have ha1 := ((ha.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hasmall := ((ha.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
    have halt : a < 1 := hasmall.trans_lt (by norm_num : (1 : ℝ) / 2 < 1)
    have hζ2 : 0 ≤ ζ ∧ ζ ≤ a ^ (2 : ℕ) := ⟨hζ.1, hζ.2.trans (by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 halt.le
        (by linarith only [hP] : (2 : ℝ) ≤ P))⟩
    obtain ⟨hs₀, _, hrad, Hprefix⟩ := HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
    obtain ⟨_, _, _, _, hk₀, _, hR₀, _, _, _, _, _, hy₀⟩ := HE₀ a ⟨ha.1, ha0⟩ θ ζ hθ hζ ρ hρ
    obtain ⟨_, _, _, _, hk₁, _, hR₁, _, _, _, _, _, hy₁⟩ := HE₁ a ⟨ha.1, ha1⟩ θ ζ hθ hζ ρ hρ
    change coreRadius (restartFastProjectiveEntry h s₁ θ ζ ρ 0)
      (restartFastProjectiveEntry h s₁ θ ζ ρ 2) = _ at hR₁
    have hq' : q₀ < q₁ := lt_of_le_of_ne hq he
    have hlog : 0 < Real.log (1 / a) :=
      Real.log_pos ((lt_div_iff₀ ha.1).mpr (by simpa only [one_mul] using halt))
    have hS : 0 < s₁ - s₀ := sub_pos.mpr
      (mul_lt_mul_of_pos_right (div_lt_div_of_pos_right hq' (by norm_num)) hlog)
    have HP : ∀ t ∈ Icc 0 (s₁ - s₀),
        0 < restartFastProjectionHeight h (t + s₀) θ ζ ρ ∧
          1 < restartFastProjectiveEntry h (t + s₀) θ ζ ρ 2 := by
      intro t ht
      have ht' : t + s₀ ∈ Icc s₀ s₁ := ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
      have H := Hprefix (t + s₀) ht'
      exact ⟨H.2.1, (by norm_num : (1 : ℝ) < 2).trans_le H.2.2⟩
    have H := restartReturn_cutoff_eventuallyEq (s := s₀) hrad hs₀ hS HP
      ((le_max_left _ _).trans hk₀) hy₀ hR₀ ((le_max_left _ _).trans hk₁)
      (by simpa only [sub_add_cancel] using hy₁) (by simpa only [sub_add_cancel] using hR₁)
    simpa only [sub_add_cancel] using H
  obtain ⟨HF, HG, HX, HT⟩ := HGerms
  refine ⟨HF, HG, HX, HT, ?_⟩
  intro n
  exact ⟨(HF.iteratedFDeriv ℝ n).self_of_nhds, (HG.iteratedFDeriv ℝ n).self_of_nhds,
    (HX.iteratedFDeriv ℝ n).self_of_nhds, (HT.iteratedFDeriv ℝ n).self_of_nhds⟩

end BianchiIX
