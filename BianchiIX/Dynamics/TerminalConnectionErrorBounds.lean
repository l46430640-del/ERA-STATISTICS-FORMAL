import BianchiIX.Analysis.TerminalPhaseComposition
import BianchiIX.Dynamics.TerminalConnectionDifferential
import BianchiIX.Dynamics.TerminalPhaseColumnInputs
import BianchiIX.Dynamics.TerminalWallFactorBounds

noncomputable section

namespace BianchiIX

/-- The amplitude-sensitive form of (D.26) and the two exceptional columns (D.27) for the exact arrival. -/
theorem exists_terminal_connection_error_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 2 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := terminalEntranceInput h Y
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionError h) Y ∧
        |terminalConnectionError h Y| ≤ C * α * z 1 * z 2 ∧
        (|fderiv ℝ (terminalConnectionError h) Y (Pi.single 0 1)| +
          |fderiv ℝ (terminalConnectionError h) Y (Pi.single 1 1)| ≤ C * z 1 * z 2 / α ^ 2) ∧
        |fderiv ℝ (terminalConnectionError h) Y (Pi.single 2 1)| ≤ C * z 1 / α ^ 2 ∧
        ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt (terminalCyclicInput h Y) Ψ ∧
        let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
        |fderiv ℝ F z (Pi.single 2 1) * terminalWallFactor h Y 1| ≤ C * z 1 / α ^ 2 ∧
        |fderiv ℝ F z (Pi.single 3 1) * terminalWallFactor h Y 0| ≤ C * z 1 * z 2 / α := by
  obtain ⟨A, hA, δ, hδ, hδhi, HI⟩ := exists_terminal_phase_column_inputs
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀small : 0 < η₀ ∧ η₀ ≤ 1 / 1000 := ⟨hη₀.1, hη₀.2.trans hδhi⟩
  have hη₀100 : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, hη₀small.2.trans (by norm_num)⟩
  obtain ⟨εi, hεi, Hinput⟩ := HI η₀ hη₀ J hJ
  obtain ⟨D, hD, εd, hεd, HD⟩ := exists_terminalEntranceInput_derivative_uniform hη₀small hJ
  obtain ⟨M, hM, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform hη₀100 hJ
  let B := D + M
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [hD, hM]
  have hDB : D ≤ B := by dsimp only [B]; linarith only [hM]
  have hMB : M ≤ B := by dsimp only [B]; linarith only [hD]
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  let C := 10 * A * B
  have hAC : A ≤ C := by
    have H := mul_le_mul_of_nonneg_left hB hA0
    dsimp only [C]
    nlinarith only [H, hA0, mul_nonneg hA0 hB0]
  have hABC : A * B ≤ C := by dsimp only [C]; nlinarith only [mul_nonneg hA0 hB0]
  refine ⟨C, hA.trans hAC, min εi (min εd εm), lt_min hεi (lt_min hεd hεm), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h z
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hη1000 : η ≤ 1 / 1000 := hηhi.trans hδhi
  have hη100 : η ≤ 1 / 100 := hη1000.trans (by norm_num)
  have hsi := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le (2 * J)))
  have hsd := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le (2 * J)))
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, HH, HU, HVwall, HW, _, Ψ, HΨ, hF, H0, Hr, Hu, Hv, Hw⟩ :=
    Hinput η α b u w hηlo hηhi hα hb hsi hsum hu hw
  change coreTailValid h Y at HV
  change 0 < projectiveCycleDenom (coreTailState h Y) at HH
  change 0 < z 1 ∧ z 1 ≤ 1 at HU
  change 0 < z 2 ∧ z 2 < 1 at HVwall
  change 0 < z 3 ∧ z 3 ≤ 1 at HW
  obtain ⟨_, Hcyc, Hcoord, _, HcoordD, _⟩ := HD η α b u w hηlo hη1000 hα hb hsd hsum
  obtain ⟨_, _, _, _, HlogU, Hfactor⟩ := HM η α b u w hηlo hη100 hα hb hsm hsum
  change ContDiffAt ℝ 2 (terminalEntranceInput h) Y at Hcoord
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have Hdiff := terminalConnectionError_differential hR HV (mul_pos hη (pow_pos hα.1 J)) HH Hcoord HΨ hF
  let F := fun x => coreRadius (entranceReturnState (Ψ x) 0) (entranceReturnState (Ψ x) 2)
  change |F z - z 0| ≤ A * α * z 1 * z 2 at H0
  change |fderiv ℝ F z (Pi.single 0 1) - 1| ≤ A * z 1 * z 2 at Hr
  change |fderiv ℝ F z (Pi.single 1 1)| ≤ A * α * z 2 at Hu
  change |fderiv ℝ F z (Pi.single 2 1)| ≤ A * z 1 at Hv
  change |fderiv ℝ F z (Pi.single 3 1)| ≤ A * α * z 1 * z 2 at Hw
  have Hnorm : ‖fderiv ℝ (terminalEntranceInput h) Y‖ ≤ B / α ^ 2 :=
    HcoordD.trans (div_le_div_of_nonneg_right hDB (sq_nonneg α))
  have Hlog : ‖fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y‖ ≤ B / α :=
    HlogU.trans (div_le_div_of_nonneg_right hMB hα.1.le)
  have HlogB (i : Fin 2) : ‖fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y‖ ≤ B / α :=
    (Hfactor i).2.2.2.2.2.trans (div_le_div_of_nonneg_right hMB hα.1.le)
  have HvalB (i : Fin 2) : |terminalWallFactor h Y i| ≤ B / α ^ 2 := by
    rw [abs_of_pos (Hfactor i).1]
    exact (Hfactor i).2.2.2.1.trans (div_le_div_of_nonneg_right hMB (sq_nonneg α))
  let p := fun j : Fin 3 => fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y (Pi.single j 1)
  let q := fun j : Fin 3 => fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y (Pi.single j 1)
  let r := fun j : Fin 3 => fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 1)) Y (Pi.single j 1)
  let s := fun j : Fin 3 => fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 0)) Y (Pi.single j 1)
  have hcol (L : ExitTailState →L[ℝ] ℝ) {K : ℝ} (hL : ‖L‖ ≤ K) (j : Fin 3) : |L (Pi.single j 1)| ≤ K := by
    have H := L.le_opNorm (Pi.single j 1)
    simp only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] at H
    exact H.trans hL
  have hp (j : Fin 3) : |p j| ≤ B / α ^ 2 := by
    dsimp only [p]
    rw [fderiv_apply (Hcoord.differentiableAt (by norm_num)) 0]
    have H := (fderiv ℝ (terminalEntranceInput h) Y).le_opNorm (Pi.single j 1)
    simp only [Pi.norm_single, norm_one, mul_one] at H
    exact (norm_le_pi_norm (fderiv ℝ (terminalEntranceInput h) Y (Pi.single j 1)) 0).trans (H.trans Hnorm)
  have HB := terminal_phase_composition_bounds p q r s hα hA0 hB0 HU.1.le
    ⟨HVwall.1.le, HVwall.2.le⟩ ⟨HW.1.le, HW.2⟩ hp (hcol _ Hlog)
    (hcol _ (HlogB 1)) (hcol _ (HlogB 0)) (HvalB 0) (HvalB 1) Hr Hu Hv Hw
  let E := fun j => (fderiv ℝ F z (Pi.single 0 1) - 1) * p j +
    fderiv ℝ F z (Pi.single 1 1) * (z 1 * q j) +
    fderiv ℝ F z (Pi.single 2 1) * (z 2 * r j) +
    fderiv ℝ F z (Pi.single 3 1) * (z 3 * s j)
  have HE0 : fderiv ℝ (terminalConnectionError h) Y (Pi.single 0 1) = E 0 := by
    rw [Hdiff.2 (Pi.single 0 1)]
    change _ + _ + fderiv ℝ F z (Pi.single 2 1) * (0 * _ + z 2 * r 0) +
      fderiv ℝ F z (Pi.single 3 1) * (0 * _ + z 3 * s 0) = E 0
    dsimp only [E, p, q]
    ring
  have HE1 : fderiv ℝ (terminalConnectionError h) Y (Pi.single 1 1) =
      E 1 + fderiv ℝ F z (Pi.single 3 1) * terminalWallFactor h Y 0 := by
    rw [Hdiff.2 (Pi.single 1 1)]
    change _ + _ + fderiv ℝ F z (Pi.single 2 1) * (0 * _ + z 2 * r 1) +
      fderiv ℝ F z (Pi.single 3 1) * (1 * _ + z 3 * s 1) = _
    dsimp only [E, p, q]
    ring
  have HE2 : fderiv ℝ (terminalConnectionError h) Y (Pi.single 2 1) =
      E 2 + fderiv ℝ F z (Pi.single 2 1) * terminalWallFactor h Y 1 := by
    rw [Hdiff.2 (Pi.single 2 1)]
    change _ + _ + fderiv ℝ F z (Pi.single 2 1) * (1 * _ + z 2 * r 2) +
      fderiv ℝ F z (Pi.single 3 1) * (0 * _ + z 3 * s 2) = _
    dsimp only [E, p, q]
    ring
  refine ⟨HV, Hdiff.1, ?_, ?_, ?_, Ψ, HΨ, ?_, ?_⟩
  · have HE := (terminalConnectionError_chart_germ HΨ Hcyc.continuousAt).self_of_nhds
    change terminalConnectionError h Y = F z - z 0 at HE
    rw [HE]
    exact H0.trans (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right hAC
      (mul_nonneg (mul_nonneg hα.1.le HU.1.le) HVwall.1.le)))
  · rw [HE0, HE1]
    exact HB.1
  · rw [HE2]
    exact HB.2.1
  · exact HB.2.2.1.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hABC HU.1.le) (sq_nonneg α))
  · exact HB.2.2.2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hABC HU.1.le) HVwall.1.le) hα.1.le)

end BianchiIX
