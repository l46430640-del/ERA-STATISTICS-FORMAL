import BianchiIX.Dynamics.EraBoundedPhase
import BianchiIX.Dynamics.TerminalNaturalAmplitude
import BianchiIX.Analysis.NegativePhaseConeTransport

noncomputable section

namespace BianchiIX

def eraOutputState (η : ℝ) (J m : ℕ) : CoreAngleState → ProjectiveState :=
  terminalNaturalState η J ∘ eraCoreExit m

def eraOutputRadius (η : ℝ) (J m : ℕ) : CoreAngleState → ℝ :=
  terminalNaturalPhase η J ∘ eraCoreExit m

/-- The actual full era contracts amplitudes and square-root cones with constants independent of its core count. -/
theorem exists_era_output_estimates :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β : ℝ) (X : CoreAngleState), 0 < β → β < 1 / 2 →
        (0 < X 1 ∧ X 1 ≤ ε / X 0) → (0 < X 2 ∧ X 2 ≤ ε / X 0) →
        X 1 + X 2 ≤ ε * (β / 2) ^ (2 * J) →
        ((m : ℝ) + 1 + β ≤ X 0 / 2 ∧ X 0 / 2 ≤ (m : ℝ) + 2 - β) →
        C * (X 1 + X 2) < β / 4 →
        let S := eraOutputState η J m
        let R := eraOutputRadius η J m
        let b₀ := X 1 + X 2
        ContDiffAt ℝ 1 S X ∧ ContDiffAt ℝ 1 R X ∧ 0 < S X 1 ∧ 0 < S X 3 ∧
        S X 1 + S X 3 ≤ C * b₀ ^ (19 / 10 : ℝ) ∧ C * b₀ ^ (7 / 24 : ℝ) < 1 / 2 ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (X 1) → |v 2| ≤ Real.sqrt (X 2) →
          let p := fderiv ℝ R X v
          p < 0 ∧
          max (|fderiv ℝ S X v 1| / (Real.sqrt (S X 1) * |p|))
            (|fderiv ℝ S X v 3| / (Real.sqrt (S X 3) * |p|)) ≤ C * b₀ ^ (7 / 24 : ℝ) := by
  obtain ⟨δ, hδ, hδmax, HT⟩ := exists_terminal_natural_cone
  obtain ⟨εk, hεk, hεkmax, K, hK, HK⟩ := exists_core_itinerary
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨A, hA, εt, hεt, HA⟩ := HT η hη hηδ J (by omega)
  obtain ⟨B, hB, εa, hεa, _, HB⟩ := exists_terminalNatural_amplitude_bound
    ⟨hη, hηδ.trans hδmax⟩ hJ
  let C := K + A + B
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC0 : 0 ≤ C := by linarith
  have hKC : K ≤ C := by dsimp [C]; linarith
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  obtain ⟨ε, hε, hεmax, Hbudget⟩ := exists_common_rpow_budget (ι := Fin 1) Finset.univ
    (C := fun _ => C) (p := fun _ => 7 / 24) (ε := fun _ => 1 / 2)
    (by intros; exact hC0) (by intros; norm_num) (by intros; norm_num)
    (lt_min hεk (lt_min hεt hεa))
  have hεk' : ε ≤ εk := hεmax.le.trans (min_le_left _ _)
  have hεt' : ε ≤ εt := hεmax.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεa' : ε ≤ εa := hεmax.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε, hεk'.trans hεkmax, C, hC, ?_⟩
  intro m β X hβ hβmax hu hw hsmall hphase hmargin S R b₀
  have hb₀ : 0 < b₀ := add_pos hu.1 hw.1
  have hk0 : 0 < X 0 := by nlinarith only [hphase.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hscale : ε / X 0 ≤ εk / X 0 := div_le_div_of_nonneg_right hεk' hk0.le
  have hcoreSmall : K * b₀ < β / 2 :=
    ((mul_le_mul_of_nonneg_right hKC hb₀.le).trans_lt hmargin).trans (by linarith)
  obtain ⟨Hall, _, _, _, hαband⟩ := HK m β X hβ hβmax
    ⟨hu.1, hu.2.trans hscale⟩ ⟨hw.1, hw.2.trans hscale⟩ hphase hcoreSmall
  obtain ⟨_, _, _, HF, _, Hwalls, Hb, _, HD⟩ := Hall m le_rfl
  let Z := eraCoreExit m X
  let α := (Z 0 - 2) / 2
  let b := Z 1 + Z 2
  change ContDiffAt ℝ 1 (eraCoreExit m) X at HF
  change (∀ i : Fin 2, 0 < Z i.succ) at Hwalls
  change b ≤ b₀ at Hb
  change 3 * β / 4 < α ∧ α < 1 - 3 * β / 4 at hαband
  have huZ : 0 < Z 1 := Hwalls 0
  have hwZ : 0 < Z 2 := Hwalls 1
  have hb : 0 < b := add_pos huZ hwZ
  have hα : 0 < α ∧ α ≤ 1 := by constructor <;> linarith only [hαband.1, hαband.2, hβ]
  have hβα : β / 2 ≤ α := by linarith only [hαband.1, hβ]
  have hs {e : ℝ} (he : ε ≤ e) : b ≤ e * α ^ (2 * J) := by
    calc
      _ ≤ b₀ := Hb
      _ ≤ ε * (β / 2) ^ (2 * J) := hsmall
      _ ≤ e * α ^ (2 * J) := mul_le_mul he
        (pow_le_pow_left₀ (half_pos hβ).le hβα _) (pow_nonneg (half_pos hβ).le _)
        (hε.le.trans he)
  have hZ : Z = ![2 + 2 * α, Z 1, Z 2] := by
    funext i
    fin_cases i
    · change Z 0 = 2 + 2 * α
      dsimp [α]
      ring
    · rfl
    · rfl
  have Hterminal := HA α b (Z 1) (Z 2) hα hb (hs hεt')
    (by rw [abs_of_pos huZ, abs_of_pos hwZ]) huZ hwZ
  have Hamp := HB α b (Z 1) (Z 2) hα hb (hs hεa')
    (by rw [abs_of_pos huZ, abs_of_pos hwZ]) huZ hwZ
  dsimp only at Hterminal Hamp
  rw [← hZ] at Hterminal Hamp
  obtain ⟨_, Hstate, Hphase, HU, HW, _, Hcone⟩ := Hterminal
  have HS : ContDiffAt ℝ 1 S X := (Hstate.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp X HF
  have HR : ContDiffAt ℝ 1 R X := (Hphase.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp X HF
  have hpow : A * b ^ (7 / 24 : ℝ) ≤ C * b₀ ^ (7 / 24 : ℝ) :=
    mul_le_mul hAC (Real.rpow_le_rpow hb.le Hb (by norm_num)) (by positivity) hC0
  have hbε : b₀ ≤ ε := hsmall.trans (mul_le_of_le_one_right hε.le
    (pow_le_one₀ (half_pos hβ).le (by linarith only [hβmax])))
  refine ⟨HS, HR, HU, HW, Hamp.2.2.trans ?_, Hbudget b₀ ⟨hb₀, hbε⟩ 0 (Finset.mem_univ _), ?_⟩
  · exact mul_le_mul hBC (Real.rpow_le_rpow hb.le Hb (by norm_num)) (by positivity) hC0
  · intro v hv0 hv1 hv2 p
    let w := fderiv ℝ (eraCoreExit m) X v
    obtain ⟨hw0, _, hwcone⟩ := HD v hv0 hv1 hv2
    let L := fderiv ℝ (terminalNaturalPhase η J) Z
    let D : CoreAngleState →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi
      ![(ContinuousLinearMap.proj 1).comp (fderiv ℝ (terminalNaturalState η J) Z),
        (ContinuousLinearMap.proj 3).comp (fderiv ℝ (terminalNaturalState η J) Z)]
    let c := C * b₀ ^ (7 / 24 : ℝ)
    have Htrans := negative_phase_cone_transport L D hw0 hwcone
      (b := ![c * Real.sqrt (S X 1), c * Real.sqrt (S X 3)]) (by
        intro z hz0 hz
        obtain ⟨hp, _, hcone⟩ := Hcone z hz0 (hz 0) (hz 1)
        have hc := hcone.trans hpow
        refine ⟨hp, ?_⟩
        intro i
        fin_cases i
        · have Hd := (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr HU) (abs_pos.mpr hp.ne))).mp
            ((le_max_left _ _).trans hc)
          exact Hd.trans_eq (by
            change c * (Real.sqrt (S X 1) * |L z|) = (c * Real.sqrt (S X 1)) * |L z|
            ring)
        · have Hd := (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr HW) (abs_pos.mpr hp.ne))).mp
            ((le_max_right _ _).trans hc)
          exact Hd.trans_eq (by
            change c * (Real.sqrt (S X 3) * |L z|) = (c * Real.sqrt (S X 3)) * |L z|
            ring))
    have hchainR : p = L w := by
      change fderiv ℝ (terminalNaturalPhase η J ∘ eraCoreExit m) X v = _
      rw [fderiv_comp X (Hphase.differentiableAt (by norm_num)) (HF.differentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply]
    have hchainS : fderiv ℝ S X v = fderiv ℝ (terminalNaturalState η J) Z w := by
      change fderiv ℝ (terminalNaturalState η J ∘ eraCoreExit m) X v = _
      rw [fderiv_comp X (Hstate.differentiableAt (by norm_num)) (HF.differentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply]
    rw [hchainR, hchainS]
    refine ⟨Htrans.1, max_le ?_ ?_⟩
    · apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr HU) (abs_pos.mpr Htrans.1.ne))).mpr
      exact (Htrans.2 0).trans_eq (by
        change (c * Real.sqrt (S X 1)) * |L w| = c * (Real.sqrt (S X 1) * |L w|)
        ring)
    · apply (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr HW) (abs_pos.mpr Htrans.1.ne))).mpr
      exact (Htrans.2 1).trans_eq (by
        change (c * Real.sqrt (S X 3)) * |L w| = c * (Real.sqrt (S X 3) * |L w|)
        ring)

end BianchiIX
