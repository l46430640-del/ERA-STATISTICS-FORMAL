import BianchiIX.Dynamics.DownwardReturnPersistence
import BianchiIX.Dynamics.EntranceDownwardPersistence
import BianchiIX.Dynamics.ShearRestartUnifiedDownwardReturn
import BianchiIX.Dynamics.ShearRestartTailCoreEntry

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The small-decaying-wall fast family has the same canonical first downward event throughout an ordinary neighborhood. -/
theorem exists_restartShear_fast_first_persistence :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          ∀ᶠ z in 𝓝 (restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ),
            IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
              projectiveOriginalFlow z 0 t 2 = 1 ∧
              normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
              (partialCoreDownwardReturnTime z) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hL, hhL, HL⟩ := exists_restartShearEntrance_inputs
  refine ⟨min hE hL, lt_min hhE hhL, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aE, haE, HAE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aL, haL, HAL⟩ := HL h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min aE aL, lt_min haE haL, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s
  let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
  obtain ⟨_, _, _, _, _, hk, _, _, hR, _, _, _, Hentry⟩ :=
    HAE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε ⟨h₂.1.le, h₂.2⟩ h₃ h₃P ρ hρ
  by_cases hv : 1 ≤ y 2
  · obtain ⟨_, _, hy, hvcase⟩ := Hentry hv
    exact (partialCoreDownwardReturn_regular hk hy hR hvcase).2.2.2.1.mono fun _ H => H.1
  · obtain ⟨_, _, _, _, hk8, _, _, hm, hu, hv', hw, hsmall⟩ :=
      HAL a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ (lt_of_not_ge hv)
    exact eventually_entrancePartialCore_downward_first hk8 hm.le
      ⟨hu.1.le, hu.2⟩ hv' hw ⟨by norm_num, le_rfl⟩ hsmall

/-- The first-event selection is also stable at the original fast cutoff of the small-growing-wall family. -/
theorem exists_restartShearTail_fast_first_persistence :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) → (0 < ν ∧ ν ≤ 2 * ε * a) →
          ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          ∀ᶠ z in 𝓝 (restartFastShearProjectiveEntry h s 1 ζ ν ρ),
            IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
              projectiveOriginalFlow z 0 t 2 = 1 ∧
              normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
              (partialCoreDownwardReturnTime z) := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨min hI hV, lt_min hhI hhV, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P
    (by linarith only [hq]) (by linarith only [hD]) hP
  refine ⟨min aI aV, lt_min haI haV, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s
  let y := restartFastShearProjectiveEntry h s 1 ζ ν ρ
  let T := shearTailTime a D
  let z := restartShearTailProjectiveEntry h a q ζ ν T ρ
  obtain ⟨_, _, hk, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, hs, hT, hrad, hc, HT, _⟩ :=
    HAV a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have hA : 0 < restartFastShearHeight h s 1 ζ ν ρ := by
    have H := (HT 0 ⟨le_rfl, hT⟩).2.2.2.2.2.2.2.2.2.1
    change a ^ 2 / 10 ≤ 1 + normalizedMaxCurve
      (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 (0 + s) 0 at H
    simpa only [restartFastShearHeight, zero_add] using (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le H
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hDen : 0 < projectiveStateDenom y :=
    toProjectiveState_denom_pos hA ((normalizedMaxCurve_constraint hdom).trans hc)
  have HN (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_normalized_flow hrad.le hs hA ht
  have HP (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  have Hend : projectiveOriginalFlow y 0 T = z := by
    have H : projectiveOriginalFlow y 0 T = toProjectiveState
        (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 (s + T)) := HP T hT
    change projectiveOriginalFlow y 0 T = toProjectiveState
      (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 (T + s))
    rw [H, add_comm s T]
  have hreg : ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
      projectiveOriginalFlow y 0 t 2 < 1 := by
    intro t ht
    refine ⟨normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hDen.ne') 0 ht.1, ?_, ?_⟩
    · rw [HN t ht.1, add_comm s t]
      exact (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le (HT t ht).2.2.2.2.2.2.2.2.2.1
    · rw [HP t ht.1, add_comm s t]
      exact (HT t ht).2.2.2.2.2.2.2.2.2.2.2
  apply partialCoreDownwardReturn_first_eventually_of_prefix hDen hT hreg
  rw [Hend]
  exact eventually_entrancePartialCore_downward_first hk hm.le
    ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ ⟨by norm_num, le_rfl⟩ hsmall

end BianchiIX
