import BianchiIX.Dynamics.DownwardReturnMovingCutoff
import BianchiIX.Dynamics.ShearRestartTailCutoff

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Every continuous choice of the auxiliary long-tail duration gives the same ordinary C2 downward event. -/
theorem exists_restartShearTail_moving_cutoff :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 128) →
          (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
          (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let y := restartFastShearProjectiveEntry h s 1 ζ ν ρ
          ∀ Θ : ProjectiveState → ℝ, ContinuousAt Θ y → Θ y = shearTailTime a D →
          (partialCoreDownwardReturnTime =ᶠ[𝓝 y]
            fun w => Θ w + partialCoreDownwardReturnTime (projectiveOriginalFlow w 0 (Θ w))) ∧
          (partialCoreDownwardReturnState =ᶠ[𝓝 y]
            fun w => partialCoreDownwardReturnState (projectiveOriginalFlow w 0 (Θ w))) ∧
          ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
          ContDiffAt ℝ 2 (fun w => Θ w + partialCoreDownwardReturnTime (projectiveOriginalFlow w 0 (Θ w))) y ∧
          ContDiffAt ℝ 2 (fun w => partialCoreDownwardReturnState (projectiveOriginalFlow w 0 (Θ w))) y ∧
          fderiv ℝ (fun w => Θ w + partialCoreDownwardReturnTime (projectiveOriginalFlow w 0 (Θ w))) y =
            fderiv ℝ partialCoreDownwardReturnTime y ∧
          fderiv ℝ (fun w => partialCoreDownwardReturnState (projectiveOriginalFlow w 0 (Θ w))) y =
            fderiv ℝ partialCoreDownwardReturnState y := by
  obtain ⟨hI, hhI, HI⟩ := exists_restartShearTail_core_inputs
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨min hI hV, lt_min hhI hhV, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aI, haI, HAI⟩ := HI h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D P
    (by linarith only [hq]) (by linarith only [hD]) hP
  refine ⟨min aI (min aV (1 / 2)), lt_min haI (lt_min haV (by norm_num)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s y Θ hcΘ hΘ
  let T := shearTailTime a D
  let z := restartShearTailProjectiveEntry h a q ζ ν T ρ
  obtain ⟨_, _, hk, _, _, hm, hu, hv, hw, hsmall, _⟩ :=
    HAI a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, hs, hTnonneg, hrad, hc, HT, _⟩ :=
    HAV a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have ha1 : a < 1 := lt_of_le_of_lt
    (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))) (by norm_num : (1 : ℝ) / 2 < 1)
  have hT : 0 < T := mul_pos (div_pos (by linarith only [hD]) ha.1)
    (Real.log_pos ((lt_div_iff₀ ha.1).mpr (by simpa only [one_mul] using ha1)))
  have hA : 0 < restartFastShearHeight h s 1 ζ ν ρ := by
    have H := (HT 0 ⟨le_rfl, hTnonneg⟩).2.2.2.2.2.2.2.2.2.1
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
        (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 (s + T)) := HP T hT.le
    change projectiveOriginalFlow y 0 T = toProjectiveState
      (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 (T + s))
    rw [H, add_comm s T]
  have hreg : ∀ t ∈ Icc 0 (Θ y), t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 := by
    rw [hΘ]
    intro t ht
    refine ⟨normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hDen.ne') 0 ht.1, ?_⟩
    rw [HN t ht.1, add_comm s t]
    have H := (HT t ht).2.2.2.2.2.2.2.2.2.1
    exact (by positivity [ha.1] : 0 < a ^ 2 / 10).trans_le H
  have hbefore : ∀ t ∈ Icc 0 (Θ y), projectiveOriginalFlow y 0 t 2 ≠ 1 ∨
      0 < normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t := by
    rw [hΘ]
    intro t ht
    apply Or.inl
    rw [HP t ht.1, add_comm s t]
    exact ((HT t ht).2.2.2.2.2.2.2.2.2.2.2).ne
  have Hnear := eventually_entrancePartialCore_downward_first hk hm.le
    ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ ⟨by norm_num, le_rfl⟩ hsmall
  have HR := entrancePartialCore_downward_regular hk hm.le
    ⟨hu.1.le, hu.2⟩ hv ⟨hw.1.le, hw.2⟩ ⟨by norm_num, le_rfl⟩ hsmall
  have Heq : projectiveOriginalFlow y 0 (Θ y) = z := by rw [hΘ]; exact Hend
  have hpos : 0 < Θ y := by rw [hΘ]; exact hT
  have HG := partialCoreDownwardReturn_moving_cutoff_eventuallyEq hDen hcΘ hpos hreg hbefore
    (by rw [Heq]; exact Hnear)
  have HC := partialCoreDownwardReturn_moving_cutoff_regular hDen hcΘ hpos hreg hbefore
    (by rw [Heq]; exact Hnear) (by rw [Heq]; exact HR.2.2.2.1) (by rw [Heq]; exact HR.2.2.2.2.1)
  exact ⟨HG.1, HG.2, HC⟩

end BianchiIX
