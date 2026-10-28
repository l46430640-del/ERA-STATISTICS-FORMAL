import BianchiIX.Dynamics.ShearRestartDownwardConnection
import BianchiIX.Dynamics.ShearRestartDownwardConeDecay
import BianchiIX.Dynamics.ConnectionRadialCurve

noncomputable section

namespace BianchiIX

open Set

/-- E.27 and the connection cone hold on the actual shear family, also at the incoming V = 1 boundary. -/
theorem exists_restartShearConnection_radial_curve :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            let τ := partialCoreDownwardReturnTime
            let out := fun r => projectiveOriginalFlow (Y r) 0 (τ (Y r))
            let f := fun r => coreRadius (out r 0) (out r 2)
            let p := fun r => coreExitConnectionParameters ![f r, out r 1, out r 3]
            let G := fun r => connectionReturnPhysicalState (p r)
            let g := fun r => G r 0
            1 ≤ Y ρ 2 →
            IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + τ (Y ρ)) ∧
            connectionReturnValid (p ρ) ∧
            connectionReturnState (p ρ) = toProjectiveState
              (normalizedMaxCurve x 0 (s + τ (Y ρ) + connectionReturnTime (p ρ))) ∧
            DifferentiableAt ℝ f ρ ∧ DifferentiableAt ℝ G ρ ∧
            (1 < f ρ ∧ 0 < g ρ) ∧ (deriv f ρ < 0 ∧ deriv g ρ < 0) ∧
            |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * p ρ 0) ∧
            (3 / 4 ≤ deriv g ρ / deriv f ρ ∧ deriv g ρ / deriv f ρ ≤ 5 / 4) ∧
            (|deriv (fun r => G r 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv g ρ| ∧
              |deriv (fun r => G r 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv g ρ|) ∧
            DifferentiableAt ℝ (fun r => 2 / f r) ρ ∧
            DifferentiableAt ℝ (fun r => 2 / g r) ρ ∧
            (0 < deriv (fun r => 2 / f r) ρ ∧ 0 < deriv (fun r => 2 / g r) ρ) ∧
            2 / g ρ - 2 / f ρ = -2 * (g ρ - f ρ) / (f ρ * g ρ) ∧
            deriv (fun r => 2 / g r) ρ / deriv (fun r => 2 / f r) ρ =
              (f ρ / g ρ) ^ 2 * (deriv g ρ / deriv f ρ) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearPartialCore_downward_cone_decay
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_downward_connection
  obtain ⟨η, hη0, hη, hsη, hηL⟩ := exists_connection_cone_threshold
  refine ⟨min hC hE, lt_min hhC hhE, ?_⟩
  intro h hh q P hq hP
  obtain ⟨C, _, HC'⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  obtain ⟨aC, haC, HaC⟩ := HC' q P hq hP 1 (by norm_num)
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP η ⟨hη0, hη⟩
  refine ⟨min aC aE, lt_min haC haE, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y x τ out f p G g hv
  obtain ⟨horig, hf, hu, hw, hdf, _, _, _, _, _, hdu, hdw, _⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  obtain ⟨_, _, hentry, hμ, hu0, hw0, _, _, hphase, hvalid, _, _, horbit, _⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let u := fun r => out r 1
  let w := fun r => out r 3
  have houtV : out ρ 2 = 1 := congrArg (fun z : ProjectiveState => z 2) hentry
  have hZ : ![f ρ, u ρ, w ρ] = partialCoreDownwardReturnState (Y ρ) := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change out ρ 3 = out ρ 2 * out ρ 3
      rw [houtV, one_mul]
  have hp : p ρ = coreExitConnectionParameters (partialCoreDownwardReturnState (Y ρ)) :=
    congrArg coreExitConnectionParameters hZ
  rw [← hp] at hμ hu0 hw0 hphase hvalid horbit
  have hphase' : phaseNorm (p ρ 0 + 1) 1 = f ρ := hphase
  have hf1 : 1 < f ρ := by
    have Hb := phaseNorm_ge (b := 1) (show 0 ≤ p ρ 0 + 1 by linarith only [hμ.1])
    rw [hphase'] at Hb
    linarith only [hμ.1, Hb]
  have hu0' : 0 < u ρ ∧ u ρ ≤ η / p ρ 0 := hu0
  have hw0' : 0 < w ρ ∧ w ρ ≤ η := hw0
  simp only [one_mul] at hdu hdw
  have hdu' : |deriv u ρ| ≤ Real.sqrt (u ρ) * |deriv f ρ| := hdu
  have hdw' : |deriv w ρ| ≤ Real.sqrt (w ρ) * |deriv f ρ| := hdw
  obtain ⟨hG, hdg, hratio, hratioBounds, hgu, hgw⟩ := connectionReturn_coreExit_curve
    hf hu hw hf1 hdf ⟨hη0, hη⟩ hsη hηL hμ.1 hu0' hw0' hdu' hdw'
  have hg : DifferentiableAt ℝ g ρ := (hasDerivAt_pi.mp hG.hasDerivAt 0).differentiableAt
  have hg0 : 0 < g ρ := by
    change 0 < Real.sqrt ((-connectionReturnState (p ρ) 0 - 1) ^ 2 + 1 ^ 2)
    positivity
  have Hrec := reciprocal_curve_identities hf hg (ne_of_gt (lt_trans (by norm_num) hf1)) hg0.ne' (ne_of_lt hdf)
  exact ⟨horig, hvalid, horbit, hf, hG, ⟨hf1, hg0⟩, ⟨hdf, hdg⟩, hratio, hratioBounds,
    ⟨hgu, hgw⟩, Hrec.1, Hrec.2.1,
    ⟨reciprocal_curve_derivative_pos hf (ne_of_gt (lt_trans (by norm_num) hf1)) hdf,
      reciprocal_curve_derivative_pos hg hg0.ne' hdg⟩, Hrec.2.2⟩

end BianchiIX
