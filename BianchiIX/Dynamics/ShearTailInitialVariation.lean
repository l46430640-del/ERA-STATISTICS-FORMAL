import BianchiIX.Dynamics.ShearRestartTailVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The actual tail starts with a bounded shear derivative and only logarithmic wall response. -/
theorem exists_restartShearTail_initial_variation :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q : ℝ, 2 < q → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 < ζ ∧ ζ ≤ 2 * ε * a) → (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let z := restartShearTailFlow h a q ζ ν 0 ρ
          let v := restartShearTailRadialVariation h a q ζ ν 0 ρ
          a ≤ 1 ∧ 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ) ∧
          q / 2 * Real.log (1 / a) ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 ∧
          positiveWalls z ∧ |v 1| ≤ 2 ∧ shearTailLogSize z v ≤ 2 + 4 * C * q * |Real.log a| := by
  simp only [restartShearTailFlow, restartShearTailRadialVariation, zero_add]
  obtain ⟨C, hC, HC⟩ := exists_restartShearCurve_sharp_control
  obtain ⟨_, _, hF, hhF, HF⟩ := exists_restartShearFastEntry_control
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, min hF (1 / (4 * C)), lt_min hhF (by positivity), ?_⟩
  intro h hh q hq
  obtain ⟨aF, haF, HFa⟩ := HF h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  obtain ⟨aB, haB, HBa⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (eventually_restart_cutoff_budget C 4 q)
  refine ⟨min aF aB, lt_min haF haB, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ
  let T := q / 2 * Real.log (1 / a)
  let Z := restartShearCurve 1 ζ ν ρ
  let z := normalizedMaxCurve (restartSectionChart h Z) 0 T
  let v := normalizedFlowDifferential (restartSectionChart h Z) 0 T (restartShearInitialVariation h ζ ν ρ)
  let p := restartSectionRadialState h T Z
  let w := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection 1)
  have HB := HBa ⟨ha.1, ha.2.trans (min_le_right _ _)⟩
  obtain ⟨ha1, hb, hT, hrad, hdom, _⟩ := HFa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    ε 1 ζ ν hε (by norm_num) ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp (hh.2.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨Hcurve, _, hn, _, _, hw, hwn, HW⟩ := HC h a T hh.1 hCh ⟨ha.1, ha1⟩ hb hT
    (by simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using HB.2.2)
    ε 1 ζ ν ρ hε (by norm_num) ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ hρ
  have Hflow := hasDerivAt_restartShearTailFlow (a := a) (q := q) (t := 0) hrad
    (by simpa only [zero_add] using hdom)
  change HasDerivAt (fun r => normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 ζ ν r)) 0 (0 + T))
    (normalizedFlowDifferential (restartSectionChart h Z) 0 (0 + T) (restartShearInitialVariation h ζ ν ρ)) ρ at Hflow
  simp only [zero_add] at Hflow
  have Hs : w.2 0 = v 1 := (hasDerivAt_pi.mp Hcurve.snd 0).unique (hasDerivAt_pi.mp Hflow 1)
  have Hfst : HasDerivAt (fun r => (restartSectionRadialState h T (restartShearCurve 1 ζ ν r)).1) w.1 ρ := Hcurve.fst
  have Hn : w.1 = v 2 := Hfst.unique (hasDerivAt_pi.mp Hflow 2)
  have Hx : w.2 1 = v 3 := (hasDerivAt_pi.mp Hcurve.snd 1).unique (hasDerivAt_pi.mp Hflow 3)
  have Hy : w.2 2 = v 4 := (hasDerivAt_pi.mp Hcurve.snd 2).unique (hasDerivAt_pi.mp Hflow 4)
  have Hz : positiveWalls z := by
    refine ⟨hn, ?_, ?_⟩
    · exact (half_pos hζ.1).trans_le (HW 0).1
    · exact (half_pos hν.1).trans_le (HW 1).1
  have hcoef : 8 * C * T = 4 * C * q * |Real.log a| := by
    dsimp only [T]
    rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos ha.1.le ha1)]
    ring
  have hcoef0 : 0 ≤ 4 * C * q * |Real.log a| := by positivity [show 0 < q by linarith only [hq]]
  change |w.1| ≤ 2 * z 2 at hwn
  refine ⟨ha1, hrad, hdom, Hz, ?_, ?_⟩
  · change |v 1| ≤ 2
    rw [← Hs]
    exact ((norm_le_pi_norm w.2 0).trans (norm_snd_le w)).trans hw
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 + 4 * C * q * |Real.log a|)).mpr
    intro i
    rw [Real.norm_eq_abs, abs_div]
    fin_cases i
    · change |v 2| / |z 2| ≤ _
      rw [abs_of_pos Hz.1, ← Hn]
      have H : |w.1| / z 2 ≤ 2 := (div_le_iff₀ Hz.1).mpr hwn
      exact H.trans (by linarith only [hcoef0])
    · change |v 3| / |z 3| ≤ _
      rw [abs_of_pos Hz.2.1, ← Hx]
      have H : |w.2 1| / z 3 ≤ 8 * C * T := (div_le_iff₀ Hz.2.1).mpr (HW 0).2.2
      rw [hcoef] at H
      linarith only [H]
    · change |v 4| / |z 4| ≤ _
      rw [abs_of_pos Hz.2.2, ← Hy]
      have H : |w.2 2| / z 4 ≤ 8 * C * T := (div_le_iff₀ Hz.2.2).mpr (HW 1).2.2
      rw [hcoef] at H
      linarith only [H]

end BianchiIX
