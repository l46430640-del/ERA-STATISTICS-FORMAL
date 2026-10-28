import BianchiIX.Dynamics.ShearRestartEntranceConnection
import BianchiIX.Dynamics.ShearRestartEntranceCoreCone
import BianchiIX.Dynamics.ConnectionRadialCurve

noncomputable section

namespace BianchiIX

open Set

/-- The fixed shear restart below V = 1 preserves the cone through the long connection
and satisfies both reciprocal-phase identities in E.27. -/
theorem exists_restartShearEntrance_connection_curve :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let f := fun r => partialCoreDownwardReturnState (Y r) 0
            let p := restartShearReturnParameters h s n₂ n₃
            let G := restartShearReturnState h s n₂ n₃
            let g := fun r => G r 0
            Y ρ 2 < 1 → ContDiffAt ℝ 2 G ρ ∧ DifferentiableAt ℝ f ρ ∧
              1 < f ρ ∧ 0 < g ρ ∧ deriv f ρ < 0 ∧ deriv g ρ < 0 ∧
              |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * p ρ 0) ∧
              (3 / 4 ≤ deriv g ρ / deriv f ρ ∧ deriv g ρ / deriv f ρ ≤ 5 / 4) ∧
              (∀ i : Fin 2, |deriv (fun r => G r i.succ) ρ| ≤ Real.sqrt (G ρ i.succ) * |deriv g ρ|) ∧
              DifferentiableAt ℝ (fun r => 2 / f r) ρ ∧
              DifferentiableAt ℝ (fun r => 2 / g r) ρ ∧
              (0 < deriv (fun r => 2 / f r) ρ ∧ 0 < deriv (fun r => 2 / g r) ρ) ∧
              2 / g ρ - 2 / f ρ = -2 * (g ρ - f ρ) / (f ρ * g ρ) ∧
              deriv (fun r => 2 / g r) ρ / deriv (fun r => 2 / f r) ρ =
                (f ρ / g ρ) ^ 2 * (deriv g ρ / deriv f ρ) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartShearEntrance_core_cone
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearEntrance_connection
  obtain ⟨η, hη0, hη, hsη, hηL⟩ := exists_connection_cone_threshold
  refine ⟨min hC hE, lt_min hhC hhE, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aC, haC, HaC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q P hq hP η ⟨hη0, hη⟩
  refine ⟨min aC aE, lt_min haC haE, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y f p G g hv
  obtain ⟨hκ, _, HZ, _, hdf, _, _, Hcone⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, _, hμ, hU, hW, _, _, hf1, _, _, _, hcG, _, _⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let Z := fun r => partialCoreDownwardReturnState (Y r)
  let u := fun r => Z r 1
  let w := fun r => Z r 2
  have hrepr (r : ℝ) : ![f r, u r, w r] = Z r := by
    ext i
    fin_cases i <;> rfl
  have hf : DifferentiableAt ℝ f ρ := differentiableAt_pi.mp HZ 0
  have hu : DifferentiableAt ℝ u ρ := differentiableAt_pi.mp HZ 1
  have hw : DifferentiableAt ℝ w ρ := differentiableAt_pi.mp HZ 2
  have Hwall (i : Fin 2) : |deriv (fun r => Z r i.succ) ρ| ≤ Real.sqrt (Z ρ i.succ) * |deriv f ρ| := by
    apply (Hcone i).trans
    have hb : 1 - 1 / (16 * coreRadius (entranceReturnState (Y ρ) 0) (entranceReturnState (Y ρ) 2)) ≤ 1 := by
      have H : 0 ≤ 1 / (16 * coreRadius (entranceReturnState (Y ρ) 0) (entranceReturnState (Y ρ) 2)) := by
        have hk0 : 0 < coreRadius (entranceReturnState (Y ρ) 0) (entranceReturnState (Y ρ) 2) := by
          linarith only [hκ]
        positivity
      linarith only [H]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)) (abs_nonneg (deriv f ρ))
  have hpρ : coreExitConnectionParameters ![f ρ, u ρ, w ρ] = p ρ := by rw [hrepr]; rfl
  have Hconn := connectionReturn_coreExit_curve hf hu hw hf1 hdf ⟨hη0, hη⟩ hsη hηL
    (by rw [hpρ]; exact hμ.1)
    (by rw [hpρ]; exact hU) hW (Hwall 0) (Hwall 1)
  have heq : (fun r => connectionReturnPhysicalState (coreExitConnectionParameters ![f r, u r, w r])) = G := by
    funext r
    rw [hrepr]
    rfl
  change DifferentiableAt ℝ (fun r => connectionReturnPhysicalState (coreExitConnectionParameters ![f r, u r, w r])) ρ ∧ _ at Hconn
  rw [heq] at Hconn
  obtain ⟨hG, hdg, hratio, hratioBounds, hgu, hgw⟩ := Hconn
  change |deriv g ρ / deriv f ρ - 1| ≤ 1 / (4 * coreExitConnectionParameters ![f ρ, u ρ, w ρ] 0) at hratio
  rw [hpρ] at hratio
  have hg : DifferentiableAt ℝ g ρ := differentiableAt_pi.mp hG 0
  have hg0 : 0 < g ρ := by
    change 0 < Real.sqrt ((-connectionReturnState (p ρ) 0 - 1) ^ 2 + 1 ^ 2)
    positivity
  have Hrec := reciprocal_curve_identities hf hg (ne_of_gt (lt_trans (by norm_num) hf1)) hg0.ne' (ne_of_lt hdf)
  have hc : ContDiffAt ℝ 2 (fun r : ℝ => ((n₂, n₃), r)) ρ := by fun_prop
  refine ⟨hcG.comp ρ hc, hf, hf1, hg0, hdf, hdg, hratio, hratioBounds, ?_, Hrec.1, Hrec.2.1,
    ⟨reciprocal_curve_derivative_pos hf (ne_of_gt (lt_trans (by norm_num) hf1)) hdf,
      reciprocal_curve_derivative_pos hg hg0.ne' hdg⟩, Hrec.2.2⟩
  intro i
  fin_cases i
  · exact hgu
  · exact hgw

end BianchiIX
