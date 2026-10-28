import BianchiIX.Dynamics.RestartPartialCoreConnection
import BianchiIX.Dynamics.RestartPartialCoreConeDecay
import BianchiIX.Dynamics.ConnectionRadialCurve

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- E.27 and cone preservation along the actual positive-wall restart family. -/
theorem exists_restartConnection_radial_curve :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                  t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
                let f := fun a => coreRadius (out a 0) (out a 2)
                let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
                let G := fun a => connectionReturnPhysicalState (p a)
                let g := fun a => G a 0
                connectionReturnValid (p ρ) ∧
                connectionReturnState (p ρ) = toProjectiveState
                  (normalizedMaxCurve x 0 (s + T + connectionReturnTime (p ρ))) ∧
                DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ G ρ ∧
                (1 < f ρ ∧ 0 < g ρ) ∧ (deriv f ρ < 0 ∧ deriv g ρ < 0) ∧
                |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * p ρ 0) ∧
                (3 / 4 ≤ deriv g ρ / deriv f ρ ∧ deriv g ρ / deriv f ρ ≤ 5 / 4) ∧
                (|deriv (fun a => G a 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv g ρ| ∧
                  |deriv (fun a => G a 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv g ρ|) ∧
                DifferentiableAt ℝ (fun a => 2 / f a) ρ ∧
                DifferentiableAt ℝ (fun a => 2 / g a) ρ ∧
                (0 < deriv (fun a => 2 / f a) ρ ∧ 0 < deriv (fun a => 2 / g a) ρ) ∧
                2 / g ρ - 2 / f ρ = -2 * (g ρ - f ρ) / (f ρ * g ρ) ∧
                deriv (fun a => 2 / g a) ρ / deriv (fun a => 2 / f a) ρ =
                  (f ρ / g ρ) ^ 2 * (deriv g ρ / deriv f ρ) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartPartialCore_cone_decay
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_connection
  obtain ⟨ε, hε0, hε, hsε, hεL⟩ := exists_connection_cone_threshold
  refine ⟨min hC hE, lt_min hhC hhE, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨C, _, HC'⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨rC, hrC, HRC⟩ := HC' q P hq hP 1 (by norm_num)
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP ε ⟨hε0, hε⟩
  refine ⟨min rC rE, lt_min hrC hrE, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  obtain ⟨T, hT, hfirst, _, τ, hτ, hcτ, hnear, hf, hu, hw, hdf, _, _, _, _, _, hdu, hdw, _⟩ :=
    HRC r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ ⟨hζ.1.le, hζ.2⟩ ρ hρ
  obtain ⟨S, _, hfirstS, _, _, hμ, hu0, hw0, _, _, hphase, hvalid, _, _, horbit⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hμ hu0 hw0 hphase hvalid horbit
  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
  let f := fun a => coreRadius (out a 0) (out a 2)
  let u := fun a => out a 1
  let w := fun a => out a 3
  let p := fun a => coreExitConnectionParameters ![f a, u a, w a]
  let G := fun a => connectionReturnPhysicalState (p a)
  let g := fun a => G a 0
  have hout : out ρ = projectiveOriginalFlow (Y ρ) 0 T := by dsimp only [out]; rw [hτ]
  have houtV : out ρ 2 = 1 := by rw [hout]; exact hfirst.1.2
  have hZ : ![f ρ, u ρ, w ρ] = toCoreAngleState (out ρ) := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change out ρ 3 = out ρ 2 * out ρ 3
      rw [houtV, one_mul]
  have hp : p ρ = coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T)) := by
    change coreExitConnectionParameters ![f ρ, u ρ, w ρ] = _
    rw [hZ, hout]
  rw [← hp] at hμ hu0 hw0 hphase hvalid horbit
  have hphase' : phaseNorm (p ρ 0 + 1) 1 = f ρ := by
    dsimp only [f]
    rw [hout]
    exact hphase
  have hf1 : 1 < f ρ := by
    have Hb := phaseNorm_ge (b := 1) (show 0 ≤ p ρ 0 + 1 by linarith only [hμ.1])
    rw [hphase'] at Hb
    linarith only [hμ.1, Hb]
  have hu0' : 0 < u ρ ∧ u ρ ≤ ε / p ρ 0 := hu0
  have hw0' : 0 < w ρ ∧ w ρ ≤ ε := hw0
  have hdu' : |deriv u ρ| ≤ Real.sqrt (u ρ) * |deriv f ρ| := by simpa only [one_mul] using hdu
  have hdw' : |deriv w ρ| ≤ Real.sqrt (w ρ) * |deriv f ρ| := by simpa only [one_mul] using hdw
  obtain ⟨hG, hdg, hratio, hratioBounds, hgu, hgw⟩ := connectionReturn_coreExit_curve
    hf hu hw hf1 hdf ⟨hε0, hε⟩ hsε hεL hμ.1 hu0' hw0' hdu' hdw'
  have hg : DifferentiableAt ℝ g ρ := (hasDerivAt_pi.mp hG.hasDerivAt 0).differentiableAt
  have hg0 : 0 < g ρ := by
    change 0 < Real.sqrt ((-connectionReturnState (p ρ) 0 - 1) ^ 2 + 1 ^ 2)
    positivity
  have Hrec := reciprocal_curve_identities hf hg (ne_of_gt (lt_trans (by norm_num) hf1)) hg0.ne' (ne_of_lt hdf)
  exact ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hvalid, horbit, hf, hG,
    ⟨hf1, hg0⟩, ⟨hdf, hdg⟩, hratio, hratioBounds, ⟨hgu, hgw⟩, Hrec.1, Hrec.2.1,
    ⟨reciprocal_curve_derivative_pos hf (ne_of_gt (lt_trans (by norm_num) hf1)) hdf,
      reciprocal_curve_derivative_pos hg hg0.ne' hdg⟩, Hrec.2.2⟩

end BianchiIX
