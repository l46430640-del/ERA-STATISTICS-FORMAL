import BianchiIX.Dynamics.ShearRestartNoDownwardCutoff
import BianchiIX.Dynamics.ShearRestartFirstPersistence
import BianchiIX.Dynamics.ShearRestartFastInterval

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The exact intermediate fast interval transfers any stable terminal event to all complete return data. -/
theorem exists_restartShear_fast_cutoff_transfer :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q₀ q₁ : ℝ, 2 < q₀ → q₀ ≤ q₁ → ∃ astar > (0 : ℝ),
        ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          ∀ ρ ∈ Icc a (2 * a),
          let s₀ := q₀ / 2 * Real.log (1 / a)
          let s₁ := q₁ / 2 * Real.log (1 / a)
          (∀ᶠ z in 𝓝 (restartFastShearProjectiveEntry h s₁ 1 n₂ n₃ ρ),
            IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
              projectiveOriginalFlow z 0 t 2 = 1 ∧
              normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
              (partialCoreDownwardReturnTime z)) →
          (fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s₀ v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((n₂, n₃), ρ)]
            (fun v => restartShearReturnParameters h s₁ v.1.1 v.1.2 v.2) ∧
          (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s₀ v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((n₂, n₃), ρ)]
            (fun v => restartShearReturnState h s₁ v.1.1 v.1.2 v.2) ∧
          (fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s₀ v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((n₂, n₃), ρ)]
            (fun v => restartShearReturnPhase h s₁ v.1.1 v.1.2 v.2) ∧
          (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s₀ v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((n₂, n₃), ρ)]
            (fun v => restartShearReturnTime h s₁ v.1.1 v.1.2 v.2) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShear_fast_interval
  refine ⟨hI, hhI, ?_⟩
  intro h hh q₀ q₁ hq₀ hq
  obtain ⟨aI, haI, HAI⟩ := HI h hh q₀ q₁ hq₀ hq
  refine ⟨min aI (1 / 2), lt_min haI (by norm_num), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ ρ hρ s₀ s₁ Hnear
  by_cases he : q₀ = q₁
  · have hs : s₀ = s₁ := by dsimp only [s₀, s₁]; rw [he]
    rw [hs]
    exact ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
  have hq' : q₀ < q₁ := lt_of_le_of_ne hq he
  obtain ⟨hs₀, _, hrad, Hprefix⟩ := HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    ε n₂ n₃ hε h₂ h₃ ρ hρ
  have ha1 : a < 1 := (ha.2.trans (min_le_right _ _)).trans_lt (by norm_num : (1 : ℝ) / 2 < 1)
  have hlog : 0 < Real.log (1 / a) :=
    Real.log_pos ((lt_div_iff₀ ha.1).mpr (by simpa only [one_mul] using ha1))
  have hS : 0 < s₁ - s₀ := sub_pos.mpr
    (mul_lt_mul_of_pos_right (div_lt_div_of_pos_right hq' (by norm_num)) hlog)
  have HP : ∀ t ∈ Icc 0 (s₁ - s₀),
      0 < restartFastShearHeight h (t + s₀) 1 n₂ n₃ ρ ∧
        (restartFastShearProjectiveEntry h (t + s₀) 1 n₂ n₃ ρ 2 ≠ 1 ∨
          0 < normalizedEventRate projectiveActiveWall
            (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 (t + s₀)) := by
    intro t ht
    have ht' : t + s₀ ∈ Icc s₀ s₁ := ⟨by linarith only [ht.1], by linarith only [ht.2]⟩
    have H := Hprefix (t + s₀) ht'
    exact ⟨H.2.1, H.2.2.2.2.2.2⟩
  have H := restartShearReturn_no_downward_cutoff_eventuallyEq (s := s₀) hrad hs₀ hS HP
    (by simpa only [sub_add_cancel] using Hnear)
  simpa only [sub_add_cancel] using H

/-- In the small-decaying-wall family every complete return germ and its iterated derivatives are cutoff-independent. -/
theorem exists_restartShear_fast_cutoff_germs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q₀ q₁ P : ℝ, 3 < q₀ → q₀ ≤ q₁ → 4 < P → ∃ astar > (0 : ℝ),
        ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s₀ := q₀ / 2 * Real.log (1 / a)
          let s₁ := q₁ / 2 * Real.log (1 / a)
          let base := ((n₂, n₃), ρ)
          let F := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartShearReturnParameters h s v.1.1 v.1.2 v.2
          let G := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartShearReturnState h s v.1.1 v.1.2 v.2
          let X := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartShearReturnPhase h s v.1.1 v.1.2 v.2
          let T := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartShearReturnTime h s v.1.1 v.1.2 v.2
          F s₀ =ᶠ[𝓝 base] F s₁ ∧ G s₀ =ᶠ[𝓝 base] G s₁ ∧
          X s₀ =ᶠ[𝓝 base] X s₁ ∧ T s₀ =ᶠ[𝓝 base] T s₁ ∧
          ∀ n : ℕ, iteratedFDeriv ℝ n (F s₀) base = iteratedFDeriv ℝ n (F s₁) base ∧
            iteratedFDeriv ℝ n (G s₀) base = iteratedFDeriv ℝ n (G s₁) base ∧
            iteratedFDeriv ℝ n (X s₀) base = iteratedFDeriv ℝ n (X s₁) base ∧
            iteratedFDeriv ℝ n (T s₀) base = iteratedFDeriv ℝ n (T s₁) base := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShear_fast_cutoff_transfer
  obtain ⟨hE, hhE, HE⟩ := exists_restartShear_fast_first_persistence
  refine ⟨min hI hE, lt_min hhI hhE, ?_⟩
  intro h hh q₀ q₁ P hq₀ hq hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    q₀ q₁ (by linarith only [hq₀]) hq
  obtain ⟨aE, haE, HAE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
    q₁ P (hq₀.trans_le hq) hP
  refine ⟨min aI aE, lt_min haI haE, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s₀ s₁ base F G X T
  have Hnear := HAE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  obtain ⟨HF, HG, HX, HT⟩ := HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ ρ hρ Hnear
  refine ⟨HF, HG, HX, HT, ?_⟩
  intro n
  exact ⟨(HF.iteratedFDeriv ℝ n).self_of_nhds, (HG.iteratedFDeriv ℝ n).self_of_nhds,
    (HX.iteratedFDeriv ℝ n).self_of_nhds, (HT.iteratedFDeriv ℝ n).self_of_nhds⟩

/-- The same cutoff-independent ordinary return germs hold when the small wall is the growing one. -/
theorem exists_restartShearTail_fast_cutoff_germs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q₀ q₁ D P : ℝ, 3 < q₀ → q₀ ≤ q₁ → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) → (0 < ν ∧ ν ≤ 2 * ε * a) →
          ∀ ρ ∈ Icc a (2 * a),
          let s₀ := q₀ / 2 * Real.log (1 / a)
          let s₁ := q₁ / 2 * Real.log (1 / a)
          let base := ((ζ, ν), ρ)
          let F := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartShearReturnParameters h s v.1.1 v.1.2 v.2
          let G := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartShearReturnState h s v.1.1 v.1.2 v.2
          let X := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartShearReturnPhase h s v.1.1 v.1.2 v.2
          let T := fun (s : ℝ) (v : (ℝ × ℝ) × ℝ) => restartShearReturnTime h s v.1.1 v.1.2 v.2
          F s₀ =ᶠ[𝓝 base] F s₁ ∧ G s₀ =ᶠ[𝓝 base] G s₁ ∧
          X s₀ =ᶠ[𝓝 base] X s₁ ∧ T s₀ =ᶠ[𝓝 base] T s₁ ∧
          ∀ n : ℕ, iteratedFDeriv ℝ n (F s₀) base = iteratedFDeriv ℝ n (F s₁) base ∧
            iteratedFDeriv ℝ n (G s₀) base = iteratedFDeriv ℝ n (G s₁) base ∧
            iteratedFDeriv ℝ n (X s₀) base = iteratedFDeriv ℝ n (X s₁) base ∧
            iteratedFDeriv ℝ n (T s₀) base = iteratedFDeriv ℝ n (T s₁) base := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShear_fast_cutoff_transfer
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearTail_fast_first_persistence
  refine ⟨min hI hE, lt_min hhI hhE, ?_⟩
  intro h hh q₀ q₁ D P hq₀ hq hD hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
    q₀ q₁ (by linarith only [hq₀]) hq
  obtain ⟨aE, haE, HAE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
    q₁ D P (hq₀.trans_le hq) hD hP
  refine ⟨min aI aE, lt_min haI haE, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s₀ s₁ base F G X T
  have Hnear := HAE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨HF, HG, HX, HT⟩ := HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    ε ζ ν ⟨hε.1, hε.2.trans (by norm_num)⟩ ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ Hnear
  refine ⟨HF, HG, HX, HT, ?_⟩
  intro n
  exact ⟨(HF.iteratedFDeriv ℝ n).self_of_nhds, (HG.iteratedFDeriv ℝ n).self_of_nhds,
    (HX.iteratedFDeriv ℝ n).self_of_nhds, (HT.iteratedFDeriv ℝ n).self_of_nhds⟩

end BianchiIX
