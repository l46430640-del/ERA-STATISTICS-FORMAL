import BianchiIX.Dynamics.RestartProjectiveEntryBounds

noncomputable section

namespace BianchiIX

open Set

def restartFastProjectiveEntry (h T θ ζ ρ : ℝ) : ProjectiveState :=
  toProjectiveState (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T)

def restartFastCoreAngle (h T θ ζ ρ : ℝ) : ℝ :=
  coreAngle (restartFastProjectiveEntry h T θ ζ ρ 0) (restartFastProjectiveEntry h T θ ζ ρ 2)

theorem differentiableAt_restartFastProjectiveEntry {h T θ ζ ρ : ℝ} {v : RestartRadialState}
    (H : HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ)
    (HA : DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ)
    (hA : restartFastProjectionHeight h T θ ζ ρ ≠ 0) :
    DifferentiableAt ℝ (restartFastProjectiveEntry h T θ ζ) ρ := by
  have Hn : DifferentiableAt ℝ (fun y => (restartSectionRadialState h T (restartRadialCurve θ ζ y)).1) ρ :=
    ((ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ H).differentiableAt
  have Hc (i : Fin 3) : DifferentiableAt ℝ
      (fun y => (restartSectionRadialState h T (restartRadialCurve θ ζ y)).2 i) ρ := by
    let P : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact (P.hasFDerivAt.comp_hasDerivAt ρ
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ H)).differentiableAt
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · exact ((Hc 0).const_mul (Real.sqrt 3)).div HA hA
  · exact (Hn.const_mul (Real.sqrt 3)).div HA hA
  · exact ((Hc 1).const_mul (Real.sqrt 3)).div HA hA
  · exact ((Hc 2).const_mul (Real.sqrt 3)).div HA hA

theorem differentiableAt_restartFastCoreAngle {h T θ ζ ρ : ℝ}
    (H : DifferentiableAt ℝ (restartFastProjectiveEntry h T θ ζ) ρ)
    (hv : restartFastProjectiveEntry h T θ ζ ρ 2 ≠ 0) :
    DifferentiableAt ℝ (restartFastCoreAngle h T θ ζ) ρ :=
  (((differentiableAt_pi.mp H 0).const_sub 1).div (differentiableAt_pi.mp H 2) hv).arsinh

/-- Every projective entry value is obtained from the exact flow; the height also has its ordinary radial derivative bound. -/
theorem exists_restartFastProjectiveEntry_bounds :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q → ∃ rstar : ℝ, 0 < rstar ∧
        ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) →
          ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let M := 8 * (L + 1)
            let y := restartFastProjectiveEntry h T θ ζ ρ
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastProjectiveEntry h T θ ζ) ρ ∧
            DifferentiableAt ℝ (restartFastCoreAngle h T θ ζ) ρ ∧
            DifferentiableAt ℝ (restartFastProjectionHeight h T θ ζ) ρ ∧
            r ^ 2 / 16 ≤ restartFastProjectionHeight h T θ ζ ρ ∧
            restartFastProjectionHeight h T θ ζ ρ ≤ 10 * (M * r) ^ 2 ∧
            |deriv (restartFastProjectionHeight h T θ ζ) ρ| ≤ 64 * M * (L + 1) * r ∧
            2 ≤ y 2 ∧ 1 / (20 * M ^ 2 * r) ≤ y 2 ∧ y 2 ≤ 32 * M / r ∧
            (0 < y 1 ∧ y 1 ≤ 32 * h * r ^ (q - 2)) ∧
            (0 ≤ y 3 ∧ y 3 ≤ 64 * ζ / r ^ 2) ∧
            (0 ≤ y 2 * y 3 ∧ y 2 * y 3 ≤ 2048 * M * ζ / r ^ 3) ∧
            |restartFastCoreAngle h T θ ζ ρ| ≤ Real.arsinh (4 * M) := by
  obtain ⟨C, hC, HC⟩ := exists_restartFastEntry_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  intro h hh L hL q hq
  obtain ⟨r₀, hr₀, HR⟩ := HC h hh L hL q hq
  let M := 8 * (L + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨min r₀ (1 / (40 * M ^ 2)), lt_min hr₀ (by positivity), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
  let y := restartFastProjectiveEntry h T θ ζ ρ
  obtain ⟨_, hsmall, hT, hrad, hdom, _, hneg, Hcurve, hnpos, hnexp, hp, ha, hb, hnsmall, hbsmall, hv, _, _⟩ :=
    HR r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨HAD, HAlo, HAhi, HAder⟩ := restartFastProjectionHeight_bounds hrad hT
    (by linarith only [hneg]) Hcurve hr.1 hp hsmall ha ⟨hnpos.le, hnsmall⟩ ⟨hb.1, hbsmall⟩ hv
  have hA : 0 < restartFastProjectionHeight h T θ ζ ρ := lt_of_lt_of_le (by positivity [hr.1]) HAlo
  have HYD := differentiableAt_restartFastProjectiveEntry Hcurve HAD (ne_of_gt hA)
  have Hs : |x 1| ≤ M * r :=
    (norm_le_pi_norm p.2 0).trans ((norm_snd_le p).trans hp)
  have Hahi : x 3 ≤ M * r :=
    (le_abs_self _).trans ((norm_le_pi_norm p.2 1).trans ((norm_snd_le p).trans hp))
  obtain ⟨HVlo, HVhi, HU, HW, Hangle⟩ := restartProjectiveEntry_bounds hr.1 hM.le hsmall HAlo HAhi Hs ⟨ha, Hahi⟩ hnpos.le hb.1
  change 1 / (20 * M ^ 2 * r) ≤ y 2 at HVlo
  change y 2 ≤ 32 * M / r at HVhi
  change 0 ≤ y 1 ∧ y 1 ≤ 32 * x 2 / r ^ 2 at HU
  change 0 ≤ y 3 ∧ y 3 ≤ 32 * x 4 / r ^ 2 at HW
  have HVtwo : 2 ≤ y 2 := by
    apply le_trans _ HVlo
    apply (le_div_iff₀ (by positivity [hr.1] : 0 < 20 * M ^ 2 * r)).mpr
    have H := (le_div_iff₀ (by positivity : 0 < 40 * M ^ 2)).mp (hr.2.trans (min_le_right _ _))
    nlinarith only [H]
  have HUpos : 0 < y 1 := by
    exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hnpos) hA
  have HUhi : y 1 ≤ 32 * h * r ^ (q - 2) := by
    calc
      _ ≤ 32 * (h * r ^ q) / r ^ 2 := HU.2.trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnexp (by norm_num)) (sq_nonneg r))
      _ = _ := by rw [Real.rpow_sub hr.1, Real.rpow_two]; ring
  have HWhi : y 3 ≤ 64 * ζ / r ^ 2 := HW.2.trans (by
    apply div_le_div_of_nonneg_right _ (sq_nonneg r)
    have Hb : x 4 ≤ 2 * ζ := hb.2
    linarith only [Hb])
  have Hp : y 2 * y 3 ≤ 2048 * M * ζ / r ^ 3 := by
    calc
      _ ≤ (32 * M / r) * (64 * ζ / r ^ 2) := mul_le_mul HVhi HWhi HW.1 (by positivity [hr.1])
      _ = _ := by ring
  have HZD := differentiableAt_restartFastCoreAngle HYD (by change y 2 ≠ 0; linarith only [HVtwo])
  refine ⟨hdom, HYD, HZD, HAD, HAlo, HAhi, ?_, HVtwo, HVlo, HVhi, ⟨HUpos, HUhi⟩,
    ⟨HW.1, HWhi⟩, ⟨mul_nonneg (by linarith only [HVtwo]) HW.1, Hp⟩, Hangle⟩
  calc
    _ ≤ 32 * (M * r) * (2 * (L + 1)) := HAder
    _ = _ := by ring

end BianchiIX
