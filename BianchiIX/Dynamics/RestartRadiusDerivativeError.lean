import BianchiIX.Dynamics.RestartRadiusVariation

noncomputable section

namespace BianchiIX

open Set

/-- Integrating the actual ordinary variation retains the decaying strong-wall factor. -/
theorem exists_restartSectionRadius_derivative_error :
    ∃ C ≥ (32 : ℝ), ∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧
      ∀ (h b T : ℝ) (Z : RestartCenterState),
        0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 →
        ‖Z‖ ≤ b / 2 → c * b ≤ restartRadialNorm Z → ∀ t ∈ Icc (0 : ℝ) T,
          DifferentiableAt ℝ (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) Z ∧
          ‖fderiv ℝ (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) Z‖ ≤
            K * (h * b + b ^ 2 * t) := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionRadius_differential_bounds
  obtain ⟨B, _, HB⟩ := exists_restartSection_fastLayer_control
  let C := max A B
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := le_max_right _ _
  have hC : 32 ≤ C := hA.trans hAC
  refine ⟨C, hC, ?_⟩
  intro c hc
  obtain ⟨K, hK, HK⟩ := HA c hc
  refine ⟨K, hK, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ hradial
  have hbpos : 0 < b := hb.1
  have hb0 : 0 ≤ b := hb.1.le
  have Hheight (k : ℝ) (hk : k ≤ C) : k * h ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hk hh.le).trans hCh
  have Htime (k : ℝ) (hk : k ≤ C) : k * b * T ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hb0) hT).trans hCb
  have H := HK h b T Z hh (Hheight A hAC) hb hT (Htime A hAC) hZ hradial
  have HF := HB h b T Z hh (Hheight B hBC) hb hT (Htime B hBC) hZ
  have hhsmall : h ≤ 1 / 16 := by nlinarith only [hC, hCh, hh]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh]) (by linarith only [hZ, hb.2])
  have Hreg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : restartSectionRadiusRegular h (Z, t) := by
    have Hn : restartSectionStrongWall h t Z ≤ 1 / 16 :=
      (HF t ht).2.1.trans ((mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (by linarith only [ht.1] : -2 * t ≤ 0)) hh.le).trans (by simpa using hhsmall))
    have HR : 0 < restartSectionRadius h t Z :=
      (by positivity : 0 < c * b / 2).trans_le (H t ht).1
    refine ⟨hrad, normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 ht.1,
      ?_, ?_, Real.sqrt_pos.mp HR⟩
    · change normalizedMaxCurve (restartSectionChart h Z) 0 t 0 < 0
      linarith only [(HF t ht).2.2.1]
    · change restartSectionStrongWall h t Z ^ 2 < 1
      have Hnpos : 0 < restartSectionStrongWall h t Z := (HF t ht).1
      nlinarith only [Hnpos, Hn]
  have Hzero := H 0 ⟨le_rfl, hT⟩
  intro t ht
  have HD := (H t ht).2.1.hasFDerivAt.sub Hzero.2.1.hasFDerivAt
  change HasFDerivAt (fun W => restartSectionRadius h t W - restartSectionRadius h 0 W) _ Z at HD
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity [ht.1])
  intro v
  have Hrate (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      |fderiv ℝ (restartSectionRadiusRate h s) Z v| ≤
        (K * ‖v‖) * ((h * b) * Real.exp (-2 * s) + b ^ 2) := by
    calc
      _ ≤ ‖fderiv ℝ (restartSectionRadiusRate h s) Z‖ * ‖v‖ :=
        (fderiv ℝ (restartSectionRadiusRate h s) Z).le_opNorm v
      _ ≤ (K * (restartSectionStrongWall h s Z * b + b ^ 2)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (H s hs).2.2.2.2 (norm_nonneg _)
      _ ≤ (K * ((h * Real.exp (-2 * s)) * b + b ^ 2)) * ‖v‖ := by
        gcongr
        exact (HF s hs).2.1
      _ = _ := by ring
  have HP := abs_sub_le_of_deriv_primitive
    (fun s hs => hasDerivAt_restartSectionRadius_variation (Hreg s hs) v)
    (fun s _ => hasDerivAt_restartFastBudget (K * ‖v‖) (h * b) (b ^ 2) s) Hrate
  have HV := HP t ht
  rw [restartFastBudget_zero, sub_zero] at HV
  have HE := restartFastBudget_le (by positivity : 0 ≤ K * ‖v‖)
    (by positivity : 0 ≤ h * b) (sq_nonneg b) (T := t) le_rfl
  change |fderiv ℝ (restartSectionRadius h t) Z v - fderiv ℝ (restartSectionRadius h 0) Z v| ≤ _
  exact HV.trans (by
    nlinarith only [HE, mul_nonneg (mul_nonneg (mul_nonneg hK.le (norm_nonneg v)) hh.le) hb0])

end BianchiIX
