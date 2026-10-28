import BianchiIX.Dynamics.ShearRestartTailRadial
import BianchiIX.Analysis.ShearTailEndpointScale

noncomputable section

namespace BianchiIX

open Set

/-- At a sufficiently late fixed endpoint, both transverse wall responses have the required linear scale. -/
theorem exists_restartShearTail_endpoint_control :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 2 < D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let z := restartShearTailFlow h a q ζ ν T ρ
            let v := restartShearTailRadialVariation h a q ζ ν T ρ
            let B := 13 + 16 * C * q + 40 * D
            a ≤ 1 / 256 ∧ 0 ≤ T + q / 2 * Real.log (1 / a) ∧
            0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ) ∧
            T + q / 2 * Real.log (1 / a) ∈
              normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 ∧
            stateConstraint z = 1 ∧ positiveWalls z ∧ shearTailRegion a z ∧ 0 < 1 + z 0 ∧
            HasDerivAt (restartShearTailFlow h a q ζ ν T) v ρ ∧
            |z 2| ≤ a ^ 2 ∧ |z 4| ≤ a ^ 2 ∧
            |v 1| ≤ B ∧ |v 3| ≤ B ∧ |v 2| ≤ B * a ∧ |v 4| ≤ B * a := by
  obtain ⟨C, hC, hR, hhR, HR⟩ := exists_restartShearTail_radial_control
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  refine ⟨C, hC, min hR (min hV 1), lt_min hhR (lt_min hhV (by norm_num)), ?_⟩
  intro h hh q D P hq hD hP
  have hD0 : 0 ≤ D := by linarith only [hD]
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD0 hP
  obtain ⟨aV, haV, HAV⟩ := HV h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q D P hq hD0 hP
  obtain ⟨an, han, HAn⟩ := exists_rpow_log_quadratic_scale hq
  obtain ⟨ay, hay, HAy⟩ := exists_rpow_log_quadratic_scale (show 2 < D / 2 + 1 by linarith only [hD])
  refine ⟨min aR (min aV (min an ay)), lt_min haR (lt_min haV (lt_min han hay)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T z v B
  obtain ⟨hasmall, hT, _, _, _, _, _, _, HRT⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, ht₀, _, hrad, _, HVT, _⟩ :=
    HAV a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  obtain ⟨ha1, Hnsmall, Hnlog⟩ := HAn a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  obtain ⟨_, Hysmall, Hylog⟩ := HAy a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  obtain ⟨HD, Hpos, HS, _, HL⟩ := HRT T ⟨hT, le_rfl⟩
  obtain ⟨Hdom, _, Hcon, Hnon, Hreg, Hn, _, Hy, _, HA, _⟩ := HVT T ⟨hT, le_rfl⟩
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have ha0 := ha.1.le
  have hh1 : h ≤ 1 := hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have Hnpow : z 2 ≤ a ^ q := Hn.trans
    ((mul_le_of_le_one_right (by positivity [hh.1] : 0 ≤ h * a ^ q)
      (Real.exp_le_one_iff.mpr (by linarith only [hT]))).trans
      (mul_le_of_le_one_left (Real.rpow_nonneg ha0 _) hh1))
  have he : Real.exp (-(a / 2) * T) = a ^ (D / 2) := by
    convert! exp_shearTailTime ha.1 (-(1 / 2)) D using 1 <;> congr 1 <;> ring
  have Hypow : z 4 ≤ a ^ (D / 2 + 1) := by
    rw [he] at Hy
    have Heps : 4 * ε ≤ 1 := by linarith only [hε.2]
    have H := mul_le_mul_of_nonneg_right Heps (by positivity [ha.1] : 0 ≤ a * a ^ (D / 2))
    rw [Real.rpow_add ha.1, Real.rpow_one]
    nlinarith only [Hy, H]
  let L := shearTailLogSize z v
  let K := 4 + 8 * C * q + 20 * D
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hKB : K ≤ B := by dsimp only [K, B]; nlinarith only [mul_nonneg hC0 hq0, hD0]
  have htime : a * T = D * |Real.log a| := by
    dsimp only [T, shearTailTime]
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) ha.1.ne', Real.log_one, zero_sub,
      abs_of_nonpos (Real.log_nonpos ha0 ha1)]
    field_simp [ha.1.ne']
  have HLa : a * L ≤ K * (1 + |Real.log a|) := by
    have H := mul_le_mul_of_nonneg_left HL ha0
    have Hs := mul_le_mul_of_nonneg_right ha1 (by positivity : 0 ≤ 8 * C * q * |Real.log a|)
    have Ht := mul_nonneg hD0 (abs_nonneg (Real.log a))
    dsimp only [K]
    change a * shearTailLogSize z v ≤ _
    nlinarith only [H, Hs, htime, ha1, mul_nonneg hC0 hq0, hD0, abs_nonneg (Real.log a)]
  have HW (i : Fin 3) (hi : 0 < z (i.addNat 2)) : |v (i.addNat 2)| ≤ z (i.addNat 2) * L := by
    have H := norm_le_pi_norm (fun j : Fin 3 => v (j.addNat 2) / z (j.addNat 2)) i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hi] at H
    simpa only [L, shearTailLogSize, mul_comm] using (div_le_iff₀ hi).mp H
  have Hnormal (i : Fin 3) (hi : 0 < z (i.addNat 2)) (p : ℝ)
      (hpow : z (i.addNat 2) ≤ a ^ p) (hlog : a ^ p * (1 + |Real.log a|) ≤ a ^ 2) :
      |v (i.addNat 2)| ≤ B * a := by
    have H0 := mul_le_mul_of_nonneg_left (HW i hi) ha0
    have H1 := mul_le_mul_of_nonneg_left HLa hi.le
    have H2 := mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ K * (1 + |Real.log a|))
    have H3 := mul_le_mul_of_nonneg_left hlog hK
    have H4 := mul_le_mul_of_nonneg_right hKB (sq_nonneg a)
    apply (mul_le_mul_iff_left₀ ha.1).mp
    nlinarith only [H0, H1, H2, H3, H4]
  have hlogsmall : a * |Real.log a| ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos ha.1) ha0
    rw [mul_sub, mul_one, mul_inv_cancel₀ ha.1.ne'] at H
    rw [abs_of_nonpos (Real.log_nonpos ha0 ha1)]
    nlinarith only [H, ha.1]
  have Hx : |v 3| ≤ B := by
    have H0 := mul_le_mul_of_nonneg_left (HW 1 Hpos.2.1) ha0
    change a * |v 3| ≤ a * (z 3 * L) at H0
    have H1 := mul_le_mul_of_nonneg_left HLa Hpos.2.1.le
    change z 3 * (a * L) ≤ z 3 * (K * (1 + |Real.log a|)) at H1
    have H2 := mul_le_mul_of_nonneg_right Hreg.2.2.2.2.1
      (by positivity : 0 ≤ K * (1 + |Real.log a|))
    change z 3 * (K * (1 + |Real.log a|)) ≤ a ^ 2 * (K * (1 + |Real.log a|)) at H2
    have Hsmall : a * (1 + |Real.log a|) ≤ 2 := by linarith only [ha1, hlogsmall]
    have H3 := mul_le_mul_of_nonneg_left Hsmall (mul_nonneg ha0 hK)
    have H4 : 2 * K ≤ B := by dsimp only [K, B]; ring_nf; linarith
    have H5 := mul_le_mul_of_nonneg_left H4 ha0
    apply (mul_le_mul_iff_left₀ ha.1).mp
    nlinarith only [H0, H1, H2, H3, H5]
  refine ⟨hasmall, add_nonneg hT ht₀, hrad, Hdom, Hcon, Hpos, Hreg,
    (by nlinarith only [HA, sq_pos_of_pos ha.1]), HD, ?_, ?_, ?_, Hx,
    Hnormal 0 Hpos.1 q Hnpow Hnlog, Hnormal 2 Hpos.2.2 (D / 2 + 1) Hypow Hylog⟩
  · rw [abs_of_pos Hpos.1]
    exact Hnpow.trans Hnsmall
  · rw [abs_of_pos Hpos.2.2]
    exact Hypow.trans Hysmall
  · exact HS.trans (by dsimp only [B]; nlinarith only [mul_nonneg hC0 hq0, hD0])

end BianchiIX
