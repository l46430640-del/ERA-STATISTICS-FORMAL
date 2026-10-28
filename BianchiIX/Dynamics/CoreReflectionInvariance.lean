import BianchiIX.Dynamics.CoreReflectionCone

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreReturn_phase_gt_one {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} (τ Y)) :
    1 < coreReturnState τ Y 0 := by
  let p := coreConnectionParameters τ Y
  obtain ⟨hy, hμ, _⟩ := coreReturn_connection_data hk hu hw hfirst
  change 1 < coreRadius (projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y) 0)
    (projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y) 2)
  rw [hy]
  change 1 < coreRadius (-p 0) 1
  have heq : coreRadius (-p 0) 1 = phaseNorm (p 0 + 1) 1 := by
    dsimp [coreRadius, coreEnergy, phaseNorm]
    congr 1
    ring
  rw [heq]
  exact lt_of_lt_of_le (by linarith only [hμ.1]) (phaseNorm_ge (by linarith only [hμ.1]))

/-- B.43 on the actual complete reflection: a common invariant amplitude domain,
positive phase orientation, and the square-root cone for every tangent vector. -/
theorem exists_large_core_reflection_invariant_cone :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ ∀ (Y : CoreAngleState), 6 ≤ Y 0 →
      (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
      ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
        (∀ᶠ X in 𝓝 Y, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry X) 0 t 2 = 1} (τ X)) ∧
        ContDiffAt ℝ 1 (coreReflectionState τ) Y ∧
        let p := coreConnectionParameters τ Y
        let Z := coreReflectionState τ Y
        connectionReturnValid p ∧ 0 < connectionReturnTime p ∧
          coreRadiusEntry Z = projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0
            (connectionReturnTime p + τ Y)) ∧
          |Z 0 - (Y 0 - 2)| ≤ 64 * (Y 1 + Y 2 ^ 2) / Y 0 ∧
          (0 < Z 1 ∧ Z 1 ≤ Y 1) ∧ (0 < Z 2 ∧ Z 2 ≤ Y 2) ∧
          (1 ≤ Y 0 - Z 0 ∧ Y 0 - Z 0 ≤ 3) ∧
          (6 ≤ Z 0 → Z 1 ≤ ε / Z 0 ∧ Z 2 ≤ ε / Z 0) ∧
          (∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
            let d := fderiv ℝ (coreReflectionState τ) Y v
            9 / 16 ≤ d 0 ∧ |d 1| ≤ Real.sqrt (Z 1) * d 0 ∧ |d 2| ≤ Real.sqrt (Z 2) * d 0) ∧
          ∀ v : CoreAngleState, |v 1| ≤ Real.sqrt (Y 1) * |v 0| →
            |v 2| ≤ Real.sqrt (Y 2) * |v 0| →
            let d := fderiv ℝ (coreReflectionState τ) Y v
            |d 1| ≤ Real.sqrt (Z 1) * |d 0| ∧ |d 2| ≤ Real.sqrt (Z 2) * |d 0| := by
  obtain ⟨εc, hεc0, hεc, Hcore⟩ := exists_large_core_invariant_cone
  obtain ⟨εl, hεl0, _, hsεl, hεlL⟩ := exists_connection_cone_threshold
  let ε := min εc εl
  have hε0 : 0 < ε := lt_min hεc0 hεl0
  have hεcore : ε ≤ εc := min_le_left _ _
  have hεconn : ε ≤ εl := min_le_right _ _
  have hε : ε ≤ 1 / 10000 := hεcore.trans hεc
  have hsε : Real.sqrt ε ≤ 1 / 1000000 := (Real.sqrt_le_sqrt hεconn).trans hsεl
  have hεL : ε ≤ Real.exp (-256) := hεconn.trans hεlL
  refine ⟨ε, hε0, hε, ?_⟩
  intro Y hk hu hw
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hu' : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hε hk0.le)⟩
  have hw' : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 :=
    ⟨hw.1, hw.2.trans (div_le_div_of_nonneg_right hε hk0.le)⟩
  obtain ⟨τ, hτ, hcτ, hcF, hnear, Hcone⟩ := Hcore Y hk
    ⟨hu.1.le, hu.2.trans (div_le_div_of_nonneg_right hεcore hk0.le)⟩
    ⟨hw.1.le, hw.2.trans (div_le_div_of_nonneg_right hεcore hk0.le)⟩
  have hfirst := hnear.mono fun _ h => h.1
  have H := coreReflection_actual_step hk hu' hw' hfirst.self_of_nhds
  have hreg := (contDiffAt_coreReflectionState hk hu' hw' hfirst.self_of_nhds hcF).2
  have hK := coreReturn_phase_gt_one hk hu' hw' hfirst.self_of_nhds
  have hdom := coreReturn_connection_domain hk ⟨hε0, hε⟩ hu hw hfirst.self_of_nhds
  have Hunit (v : CoreAngleState) (hv : v 0 = 1)
      (hvu : |v 1| ≤ Real.sqrt (Y 1)) (hvw : |v 2| ≤ Real.sqrt (Y 2)) :
      let d := fderiv ℝ (coreReflectionState τ) Y v
      9 / 16 ≤ d 0 ∧
        |d 1| ≤ Real.sqrt (coreReflectionState τ Y 1) * d 0 ∧
        |d 2| ≤ Real.sqrt (coreReflectionState τ Y 2) * d 0 := by
    intro d
    let ξ := fderiv ℝ (coreReturnState τ) Y v
    have Hi := Hcone v hv hvu hvw
    have hξ0 : 0 < ξ 0 := Hi.1
    have hξmin : 3 / 4 ≤ ξ 0 := by
      have hb : 1 / (32 * Y 0) ≤ 1 / 4 :=
        (div_le_iff₀ (by positivity : 0 < 32 * Y 0)).mpr (by linarith only [hk])
      linarith only [(abs_le.mp Hi.2.1).1, hb]
    have hfactor : 1 - 1 / (16 * Y 0) ≤ 1 := sub_le_self _ (by positivity)
    have hξu : |ξ 1| ≤ Real.sqrt (coreReturnState τ Y 1) * ξ 0 := Hi.2.2.1.trans (by
      change (1 - 1 / (16 * Y 0)) * Real.sqrt (coreReturnState τ Y 1) * ξ 0 ≤ _
      nlinarith only [mul_le_mul_of_nonneg_right hfactor
        (mul_nonneg (Real.sqrt_nonneg (coreReturnState τ Y 1)) hξ0.le)])
    have hξw : |ξ 2| ≤ Real.sqrt (coreReturnState τ Y 2) * ξ 0 := Hi.2.2.2.trans (by
      change (1 - 1 / (16 * Y 0)) * Real.sqrt (coreReturnState τ Y 2) * ξ 0 ≤ _
      nlinarith only [mul_le_mul_of_nonneg_right hfactor
        (mul_nonneg (Real.sqrt_nonneg (coreReturnState τ Y 2)) hξ0.le)])
    have HT := coreReflection_cone_transport hK (hcF.differentiableAt (by norm_num))
      ⟨hε0, hε⟩ hsε hεL hdom.1 hdom.2.1 hdom.2.2 hξ0 hξu hξw
    exact ⟨by linarith only [HT.1, hξmin], HT.2⟩
  refine ⟨τ, hτ, hcτ, hfirst, hreg, H.1, H.2.1, H.2.2.1, H.2.2.2.1,
    H.2.2.2.2.1, H.2.2.2.2.2.1, H.2.2.2.2.2.2, ?_, Hunit, ?_⟩
  · intro hn
    have hnk : coreReflectionState τ Y 0 ≤ Y 0 := by linarith only [H.2.2.2.2.2.2.1]
    have hdiv := div_le_div_of_nonneg_left hε0.le
      (by linarith only [hn] : 0 < coreReflectionState τ Y 0) hnk
    exact ⟨H.2.2.2.2.1.2.trans (hu.2.trans hdiv), H.2.2.2.2.2.1.2.trans (hw.2.trans hdiv)⟩
  · intro v hvu hvw
    have Hall := homogeneous_cone_of_unit (fderiv ℝ (coreReflectionState τ) Y)
      (R := 1) (by norm_num) (a := Real.sqrt (Y 1)) (b := Real.sqrt (Y 2))
      (A := Real.sqrt (coreReflectionState τ Y 1)) (B := Real.sqrt (coreReflectionState τ Y 2)) (by
        intro z hz hzu hzw
        have Hz := Hunit z (by simpa only [one_mul] using hz) hzu hzw
        exact ⟨by linarith only [Hz.1], Hz.2⟩) v
      (by simpa only [one_mul] using hvu) (by simpa only [one_mul] using hvw)
    exact Hall

end BianchiIX
