import BianchiIX.Dynamics.PartialCoreDownwardReturn
import BianchiIX.Dynamics.ShearRestartPartialCoreResponse

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The canonical downward return and its ambient derivative apply to every actual shear entry with V at least one. -/
theorem exists_restartShearPartialCore_downward_return :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
            let k := restartFastShearCoreRadius h s 1 n₂ n₃ ρ
            let T := partialCoreDownwardReturnTime y
            1 ≤ y 2 →
            s ∈ normalizedMaxDomain x 0 ∧ 0 < T ∧
            IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + T) ∧
            partialCoreDownwardReturnState y =
              toCoreAngleState (toProjectiveState (normalizedMaxCurve x 0 (s + T))) ∧
            ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧
            ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
            (∀ᶠ z in 𝓝 y,
              IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
                projectiveOriginalFlow z 0 t 2 = 1 ∧
                normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
                  (partialCoreDownwardReturnTime z) ∧
              ∀ t ∈ Icc 0 (partialCoreDownwardReturnTime z), t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
                0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0) ∧
            ∀ w : ProjectiveState,
              let v := fderiv ℝ toCoreAngleState y w
              let dz := fderiv ℝ projectiveCoreAngle y w
              |(fderiv ℝ partialCoreDownwardReturnState y w) 0 - v 0| ≤ 4096 * coreVariationBound *
                (|v 1| + (y 1 + y 2 * y 3) * (|v 0| + |v 2|) / k +
                  (k * y 1 + (y 2 * y 3) ^ 2 / k) * |dz|) := by
  obtain ⟨hstar, hhstar, H⟩ := exists_restartShearPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := H h hh q P hq hP (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s x y k T hv
  obtain ⟨hs, hrad, hdom, hA, _, hk, _, _, hR, _, _, _, Hentry⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ
  obtain ⟨_, _, hregion, hvcase⟩ := Hentry hv
  have HR := partialCoreDownwardReturn_regular hk hregion hR hvcase
  have hT : 0 < T := HR.1.1.1
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  have Hfirst : IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + T) := by
    refine ⟨⟨by linarith only [hT], ?_⟩, ?_⟩
    · rw [← Hflow T hT.le]
      exact HR.1.1.2
    · intro t ht
      have hsub : 0 < t - s := sub_pos.mpr ht.1
      have HF := Hflow (t - s) hsub.le
      rw [add_sub_cancel] at HF
      have Hleast := HR.1.2 ⟨hsub, by rw [HF]; exact ht.2⟩
      linarith only [Hleast]
  have Hstate : partialCoreDownwardReturnState y =
      toCoreAngleState (toProjectiveState (normalizedMaxCurve x 0 (s + T))) := by
    change toCoreAngleState (projectiveOriginalFlow y 0 T) = _
    rw [Hflow T hT.le]
  exact ⟨hdom, hT, Hfirst, Hstate, HR.2⟩

end BianchiIX
