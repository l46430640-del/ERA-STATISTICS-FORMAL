import BianchiIX.Dynamics.CoreDownwardIdentification
import BianchiIX.Dynamics.CoreConeInvariance
import BianchiIX.Analysis.HomogeneousPhase

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The fixed full-core return retains both the radial error and the strict wall-cone margin. -/
theorem exists_coreRadiusReturn_large_cone_margin :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ Y : CoreAngleState, 6 ≤ Y 0 →
      (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
      ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let F := coreReturnState coreRadiusReturnTime
        let d := fderiv ℝ F Y v
        0 < d 0 ∧ |d 0 - 1| ≤ 1 / (32 * Y 0) ∧
          ∀ i : Fin 2, |d i.succ| ≤
            (1 - 1 / (16 * Y 0)) * Real.sqrt (F Y i.succ) * d 0 := by
  obtain ⟨ε, hε, hεsmall, Hε⟩ := exists_large_core_invariant_cone
  refine ⟨ε, hε, hεsmall, ?_⟩
  intro Y hk hu hw
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hsmall := div_le_div_of_nonneg_right hεsmall hk0.le
  have hu' := And.intro hu.1 (hu.2.trans hsmall)
  have hw' := And.intro hw.1 (hw.2.trans hsmall)
  obtain ⟨τ, _, _, _, hnear, Hcone⟩ := Hε Y hk hu hw
  have hcanonical := (coreRadiusReturn_large_regular hk hu' hw').2.2.2
  have htime : coreRadiusReturnTime =ᶠ[𝓝 Y] τ := by
    filter_upwards [hcanonical, hnear] with Z hc ht
    exact hc.unique ht.1
  have hstate : coreReturnState coreRadiusReturnTime =ᶠ[𝓝 Y] coreReturnState τ := by
    filter_upwards [htime] with Z hZ
    simp only [coreReturnState, hZ]
  refine ⟨(coreRadiusReturn_large_contDiff_two hk hu' hw').2, ?_⟩
  intro v hv0 hv1 hv2 F d
  obtain ⟨hpos, hrad, hc1, hc2⟩ := Hcone v hv0 hv1 hv2
  have hderiv : d = fderiv ℝ (coreReturnState τ) Y v := by
    dsimp only [d, F]
    rw [hstate.fderiv_eq]
  rw [hderiv]
  refine ⟨hpos, hrad, ?_⟩
  intro i
  change |fderiv ℝ (coreReturnState τ) Y v i.succ| ≤
    (1 - 1 / (16 * Y 0)) * Real.sqrt (coreReturnState coreRadiusReturnTime Y i.succ) *
      fderiv ℝ (coreReturnState τ) Y v 0
  rw [hstate.self_of_nhds]
  fin_cases i
  · exact hc1
  · exact hc2

/-- Curves with decreasing radius traverse the fixed core with controlled slope and a narrower cone. -/
theorem exists_coreRadiusReturn_curve_cone :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ (Y : ℝ → CoreAngleState) (x : ℝ),
      DifferentiableAt ℝ Y x → 6 ≤ Y x 0 →
      (0 ≤ Y x 1 ∧ Y x 1 ≤ ε / Y x 0) → (0 ≤ Y x 2 ∧ Y x 2 ≤ ε / Y x 0) →
      deriv (fun t => Y t 0) x < 0 →
      (∀ i : Fin 2, |deriv (fun t => Y t i.succ) x| ≤
        Real.sqrt (Y x i.succ) * |deriv (fun t => Y t 0) x|) →
      let G := fun t => coreReturnState coreRadiusReturnTime (Y t)
      DifferentiableAt ℝ G x ∧ deriv (fun t => G t 0) x < 0 ∧
        |deriv (fun t => G t 0) x / deriv (fun t => Y t 0) x - 1| ≤ 1 / (32 * Y x 0) ∧
        (3 / 4 ≤ deriv (fun t => G t 0) x / deriv (fun t => Y t 0) x ∧
          deriv (fun t => G t 0) x / deriv (fun t => Y t 0) x ≤ 5 / 4) ∧
        ∀ i : Fin 2, |deriv (fun t => G t i.succ) x| ≤
          (1 - 1 / (16 * Y x 0)) * Real.sqrt (G x i.succ) * |deriv (fun t => G t 0) x| := by
  obtain ⟨ε, hε, hεsmall, Hε⟩ := exists_coreRadiusReturn_large_cone_margin
  refine ⟨ε, hε, hεsmall, ?_⟩
  intro Y x hY hk hu hw hneg hwall G
  obtain ⟨hF, Hunit⟩ := Hε (Y x) hk hu hw
  let D := fderiv ℝ (coreReturnState coreRadiusReturnTime) (Y x)
  let v := deriv Y x
  have hv (i : Fin 3) : deriv (fun t => Y t i) x = v i :=
    (hasDerivAt_pi.mp hY.hasDerivAt i).deriv
  have HD : HasDerivAt G (D v) x :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
  have hd (i : Fin 3) : deriv (fun t => G t i) x = D v i :=
    (hasDerivAt_pi.mp HD i).deriv
  have hvneg : v 0 < 0 := by rwa [hv 0] at hneg
  have hva : |v 1| ≤ Real.sqrt (Y x 1) * |(1 : ℝ) * v 0| := by
    simpa [hv] using hwall 0
  have hvb : |v 2| ≤ Real.sqrt (Y x 2) * |(1 : ℝ) * v 0| := by
    simpa [hv] using hwall 1
  have HR := homogeneous_phase_ratio_of_unit D (R := 1)
    (fun z hz hzu hzw => (Hunit z (by simpa only [one_mul] using hz) hzu hzw).2.1)
    v (by simpa only [one_mul] using hvneg.ne) hva hvb
  have HC := homogeneous_cone_of_unit D (R := 1) (by norm_num)
    (A := (1 - 1 / (16 * Y x 0)) * Real.sqrt (G x 1))
    (B := (1 - 1 / (16 * Y x 0)) * Real.sqrt (G x 2))
    (fun z hz hzu hzw => by
      have H := Hunit z (by simpa only [one_mul] using hz) hzu hzw
      exact ⟨H.1.le, H.2.2 0, H.2.2 1⟩) v hva hvb
  simp only [one_mul] at HR
  have hsmall : 1 / (32 * Y x 0) ≤ (1 / 4 : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith only [hk]
  have Hbounds : 3 / 4 ≤ D v 0 / v 0 ∧ D v 0 / v 0 ≤ 5 / 4 := by
    have H := abs_le.mp (HR.trans hsmall)
    constructor <;> linarith only [H.1, H.2]
  have Hneg : D v 0 < 0 := by
    have Hpos : 0 < D v 0 / v 0 := lt_of_lt_of_le (by norm_num) Hbounds.1
    exact ((div_pos_iff.mp Hpos).resolve_left (fun h => (not_lt_of_ge hvneg.le) h.2)).1
  refine ⟨HD.differentiableAt, ?_, ?_, ?_, ?_⟩
  · rwa [hd]
  · simpa only [hd, hv] using HR
  · simpa only [hd, hv] using Hbounds
  · intro i
    simp only [hd]
    fin_cases i
    · exact HC.1
    · exact HC.2

end BianchiIX
