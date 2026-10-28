import BianchiIX.Dynamics.ExitSinglePhaseDerivativeBounds
import BianchiIX.Dynamics.ExitTailHeightGeometry

noncomputable section

namespace BianchiIX

/-- The single-wall phase at the actual endpoint has uniform fixed-height derivatives (D.28). -/
theorem exists_terminal_single_phase_bounds {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let y := coreTailState h Y
      let Z := toExitTailState y
      let β := |y 1| + |y 3|
      let f := fun Q : ExitTailState => exitSinglePhase (Q 0) (Q 1) h (Q 2)
      coreTailValid h Y ∧
        f Z = singleStrongPhase (projectiveCycle y 0) (projectiveCycle y 1) ∧
        ContDiffAt ℝ 2 f Z ∧
        |fderiv ℝ f Z (Pi.single 0 1) - 1 / 2| ≤ 1024 * β * (h + β) / α ^ 2 ∧
        |fderiv ℝ f Z (Pi.single 1 1)| + |fderiv ℝ f Z (Pi.single 2 1)| ≤ 1024 * (h + β) / α := by
  obtain ⟨A, hA, ε, hε, HG⟩ := exists_terminal_tail_geometry_uniform hη₀ hJ
  refine ⟨ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h y Z β f
  obtain ⟨HV, hm, HR, Hwall, HB, hv, _⟩ := HG η α b u w hηlo hηhi hα hb hsmall hsum
  change coreTailValid h Y at HV
  change y 0 < 1 at hm
  change |Z 0 - (2 + 2 * α)| ≤ A * b at HR
  change β ≤ A * b at Hwall
  have Hactive : y 2 = h := coreTailState_active HV
  change 0 ≤ y 2 ∧ y 2 ≤ α / 100 at hv
  rw [Hactive] at hv
  have Hwall' : |Z 1| + |Z 2| ≤ β := le_refl β
  have HD := exitSinglePhase_derivative_bounds hα (Hwall.trans HB) (HR.trans HB) Hwall' hv
  change ContDiffAt ℝ 2 f Z ∧ _ at HD
  refine ⟨HV, ?_, HD⟩
  obtain ⟨_, _, _, _, Hsq, HH, _, _, HHpos, HNpos⟩ :=
    exitSingle_terminal_geometry hα (Hwall.trans HB) (HR.trans HB) Hwall' hv
  have hα0 := hα.1
  have HH₀ : 0 < exitSingleBase (Z 0) h := lt_of_lt_of_le (sq_pos_of_pos hα0) HH
  have HE := exitSinglePhase_eq_singleStrongPhase Hsq.le HH₀ HHpos HNpos
  change f Z = _ at HE
  have Hreconstruct : fromExitTailState h Z = y := by
    rw [← Hactive]
    exact fromExitTailState_toExitTailState hm
  rw [← Hreconstruct]
  convert HE using 1; dsimp [projectiveCycle, projectiveCycleDenom, fromExitTailState]
  congr 2; ring

end BianchiIX
