import BianchiIX.Dynamics.EraAmplitudeExtension
import BianchiIX.Analysis.RadiusAmplitudeWindowMeasurability
import BianchiIX.Analysis.MeasurableComposition

noncomputable section

namespace BianchiIX

open Set

set_option maxHeartbeats 800000 in
/-- Actual era outputs and the same extended amplitudes and slopes are jointly Borel in arbitrary standard Borel labels. -/
theorem exists_era_amplitude_extension_measurable {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β B : X → ℝ) (U W : X → ℝ → ℝ), Measurable β →
        (∀ q, 0 < β q) → (∀ q, β q < 1 / 4) →
        let a := fun q => 2 * ((m : ℝ) + 1 + β q)
        let b := fun q => 2 * ((m : ℝ) + 2 - β q)
        (∀ q, B q * b q ≤ ε) → (∀ q, B q ≤ ε * (β q / 2) ^ (2 * J)) →
        (∀ q, C * B q < β q / 4) →
        Measurable (fun p : closedIntervalFamily a b => U p.val.1 p.val.2) →
        Measurable (fun p : closedIntervalFamily a b => W p.val.1 p.val.2) →
        (∀ q r, r ∈ Icc (a q) (b q) → 0 < U q r ∧ 0 < W q r ∧ U q r + W q r ≤ B q ∧
          ContDiffAt ℝ 1 (U q) r ∧ ContDiffAt ℝ 1 (W q) r ∧
          |deriv (U q) r| ≤ Real.sqrt (U q r) ∧ |deriv (W q) r| ≤ Real.sqrt (W q r)) →
        Measurable (fun p : closedIntervalFamily a b =>
          eraOutputState η J m ![p.val.2, U p.val.1 p.val.2, W p.val.1 p.val.2]) ∧
        Measurable (fun p : closedIntervalFamily a b =>
          eraGraphRadius η J m (U p.val.1) (W p.val.1) p.val.2) ∧
        ∀ i : Fin 4, (i = 1 ∨ i = 3) →
          Measurable (fun p : X × ℝ => eraAmplitudeExtension η J m (β p.1) (U p.1) (W p.1) i p.2) ∧
          Measurable (fun p : X × ℝ => deriv (eraAmplitudeExtension η J m (β p.1) (U p.1) (W p.1) i) p.2) := by
  obtain ⟨δo, hδo, hδomax, HO⟩ := exists_era_output_estimates
  obtain ⟨δi, hδi, _, HI⟩ := exists_era_interval_inverse
  refine ⟨min δo δi, lt_min hδo hδi, (min_le_left _ _).trans hδomax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨εo, hεo, hεomax, Co, hCo, HEO⟩ := HO η hη (hηδ.trans (min_le_left _ _)) J hJ
  obtain ⟨εi, hεi, _, Ci, hCi, HEI⟩ := HI η hη (hηδ.trans (min_le_right _ _)) J (by omega)
  let ε := min εo εi
  let C := Co + Ci
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCoC : Co ≤ C := by dsimp [C]; linarith
  have hCiC : Ci ≤ C := by dsimp [C]; linarith
  have heo : ε ≤ εo := min_le_left _ _
  have hei : ε ≤ εi := min_le_right _ _
  refine ⟨ε, lt_min hεo hεi, heo.trans hεomax, C, hC, ?_⟩
  intro m β B U W hβm hβ hβmax a b hscale hsmall hmargin hUm hWm Hgraph
  have ha : Measurable a := (measurable_const.add hβm).const_mul 2
  have hb : Measurable b := (measurable_const.sub hβm).const_mul 2
  have hab (q : X) : a q < b q := by dsimp [a, b]; linarith [hβmax q]
  let D := closedIntervalFamily a b
  let A (q : X) (r : ℝ) : CoreAngleState := ![r, U q r, W q r]
  let k (q : X) := eraGraphRadius η J m (U q) (W q)
  let S := eraOutputState η J m
  let R := eraOutputRadius η J m
  have Hactual (q : X) (r : ℝ) (hr : r ∈ Icc (a q) (b q)) :
      ContDiffAt ℝ 1 S (A q r) ∧ ContDiffAt ℝ 1 R (A q r) ∧
      0 < S (A q r) 1 ∧ 0 < S (A q r) 3 ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (U q r) →
        |v 2| ≤ Real.sqrt (W q r) → fderiv ℝ R (A q r) v < 0 := by
    obtain ⟨hu, hw, hsum, _⟩ := Hgraph q r hr
    have hB : 0 < B q := by linarith
    have hr0 : 0 < r := by dsimp [a] at hr; nlinarith [hr.1, hβ q, Nat.cast_nonneg (α := ℝ) m]
    have hBr : B q * r ≤ εo := ((mul_le_mul_of_nonneg_left hr.2 hB.le).trans (hscale q)).trans heo
    have hwall {z : ℝ} (hz : z ≤ B q) : z ≤ εo / r :=
      (le_div_iff₀ hr0).mpr ((mul_le_mul_of_nonneg_right hz hr0.le).trans hBr)
    have hphase : (m : ℝ) + 1 + β q ≤ r / 2 ∧ r / 2 ≤ (m : ℝ) + 2 - β q := by
      dsimp [a, b] at hr
      constructor <;> linarith [hr.1, hr.2]
    have hUB : U q r ≤ B q := by linarith
    have hWB : W q r ≤ B q := by linarith
    have hsmallo : U q r + W q r ≤ εo * (β q / 2) ^ (2 * J) :=
      (hsum.trans (hsmall q)).trans (mul_le_mul_of_nonneg_right heo (pow_nonneg (half_pos (hβ q)).le _))
    have hmargin' : Co * (U q r + W q r) < β q / 4 :=
      ((mul_le_mul_of_nonneg_left hsum (by linarith : 0 ≤ Co)).trans
        (mul_le_mul_of_nonneg_right hCoC hB.le)).trans_lt (hmargin q)
    obtain ⟨HS, HR, hu', hw', _, _, HD⟩ := HEO m (β q) (A q r) (hβ q) (by linarith [hβmax q])
      ⟨hu, hwall hUB⟩ ⟨hw, hwall hWB⟩ hsmallo hphase hmargin'
    exact ⟨HS, HR, hu', hw', fun v h0 h1 h2 => (HD v h0 h1 h2).1⟩
  have hAm : Measurable (fun p : D => A p.val.1 p.val.2) := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact measurable_snd.comp measurable_subtype_coe
    · exact hUm
    · exact hWm
  have hSm : Measurable (fun p : D => S (A p.val.1 p.val.2)) :=
    measurable_comp_of_continuousAt (f := S) (g := fun p : D => A p.val.1 p.val.2)
      hAm (fun p => (Hactual p.val.1 p.val.2 p.property).1.continuousAt)
  have hkm : Measurable (fun p : D => k p.val.1 p.val.2) :=
    measurable_comp_of_continuousAt (f := R) (g := fun p : D => A p.val.1 p.val.2)
      hAm (fun p => (Hactual p.val.1 p.val.2 p.property).2.1.continuousAt)
  have Hk (q : X) (r : ℝ) (hr : r ∈ Icc (a q) (b q)) :
      ContDiffAt ℝ 1 (k q) r ∧ deriv (k q) r < 0 := by
    obtain ⟨_, _, _, hU, hW, hdU, hdW⟩ := Hgraph q r hr
    obtain ⟨hc, hd⟩ := graphPhase_differential (Hactual q r hr).2.1 hU hW
    refine ⟨hc, ?_⟩
    change deriv (graphPhase R (U q) (W q)) r < 0
    rw [hd.deriv]
    exact (Hactual q r hr).2.2.2.2 ![1, deriv (U q) r, deriv (W q) r] rfl hdU hdW
  have hden (q : X) : 0 < 1 - 2 * β q := by linarith [hβmax q]
  let l := fun q => 2 / (1 - 2 * β q)
  let r := fun q => 1 / β q
  have hlr (q : X) : l q < r q := (div_lt_div_iff₀ (hden q) (hβ q)).mpr (by nlinarith [hβmax q])
  have hwindow (q : X) : Icc (l q) (r q) ⊆ Icc (k q (b q)) (k q (a q)) := by
    have hB : 0 < B q := by
      obtain ⟨hu, hw, hsum, _⟩ := Hgraph q (a q) ⟨le_rfl, (hab q).le⟩
      linarith
    have hsmalli : B q ≤ εi * (β q / 2) ^ (2 * J) := (hsmall q).trans
      (mul_le_mul_of_nonneg_right hei (pow_nonneg (half_pos (hβ q)).le _))
    obtain ⟨_, _, hfa, hfb, _⟩ := HEI m (β q) (B q) (U q) (W q) (hβ q) (hβmax q)
      ((hscale q).trans hei) hsmalli ((mul_le_mul_of_nonneg_right hCiC hB.le).trans_lt (hmargin q)) (Hgraph q)
    change 2 / k q (a q) < 2 * β q at hfa
    change 1 - 2 * β q < 2 / k q (b q) at hfb
    have hba := (intervalRadiusInverse_control (hab q) (fun x hx => (Hk q x hx).1)
      (fun x hx => (Hk q x hx).2)).1
    have hkb : 0 < k q (b q) := by
      by_contra! hn
      have Hnon := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2) hn
      linarith [hden q]
    have hka : 0 < k q (a q) := hkb.trans hba
    have hkl : k q (b q) < l q := by
      have H := (lt_div_iff₀ hkb).mp hfb
      exact (lt_div_iff₀ (hden q)).mpr (by nlinarith)
    have hkr : r q < k q (a q) := by
      have H := (div_lt_iff₀ hka).mp hfa
      exact (div_lt_iff₀ (hβ q)).mpr (by nlinarith)
    exact fun _ hx => ⟨hkl.le.trans hx.1, hx.2.trans hkr.le⟩
  refine ⟨hSm, hkm, ?_⟩
  intro i hi
  let V (q : X) := eraGraphWall η J m (U q) (W q) i
  have hVm : Measurable (fun p : D => V p.val.1 p.val.2) :=
    (measurable_pi_apply i).comp hSm
  have hV (q : X) (s : ℝ) (hs : s ∈ Icc (a q) (b q)) : ContDiffAt ℝ 1 (V q) s :=
    (graphPhase_differential (contDiffAt_pi.mp (Hactual q s hs).1 i)
      (Hgraph q s hs).2.2.2.1 (Hgraph q s hs).2.2.2.2.1).1
  have hpos (q : X) (s : ℝ) (hs : s ∈ Icc (a q) (b q)) : 0 < V q s := by
    rcases hi with rfl | rfl
    · exact (Hactual q s hs).2.2.1
    · exact (Hactual q s hs).2.2.2.1
  exact jointly_measurable_radiusAmplitudeWindowExtension ha hb hab (k := k) (U := V)
    (l := l) (r := r) (measurable_const.div (measurable_const.sub (hβm.const_mul 2)))
    (measurable_const.div hβm) hlr
    hwindow hkm hVm (fun q s hs => (Hk q s hs).1) (fun q s hs => (Hk q s hs).2) hV hpos

end BianchiIX
