import BianchiIX.Dynamics.PhysicalEntranceCore

noncomputable section

namespace BianchiIX

open Set

/-- The compact reference family controls the genuine physical first core, with a positive wall floor. -/
theorem exists_compact_physicalEntrance_core {K a : ℝ} (ha : 0 < a) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ k ∈ Icc 2 K, ∀ v ∈ Icc a (1 / 2),
      ∀ x : NormalizedState, stateConstraint x = 1 →
        normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) x ≤ δ →
        let T := (physicalEntranceData x).1
        let X := normalizedMaxCurve x 0 T
        let Y := toProjectiveState X
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
          T ≤ C ∧ Y 2 = 1 ∧ 1 < Y 0 ∧ 0 < 1 + X 0 ∧
          |coreRadius (Y 0) (Y 2) - k| ≤
            C * normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) x ∧
          referenceCoreWallFloor K ≤ X 3 ∧
          HasDerivAt (fun t => projectiveActiveWall (normalizedMaxCurve x 0 t))
            (normalizedEventRate projectiveActiveWall x 0 T) T ∧
          0 < normalizedEventRate projectiveActiveWall x 0 T ∧
          ContDiffAt ℝ 2 physicalEntranceData x := by
  obtain ⟨δ₀, hδ₀, C, hC, H⟩ := exists_compact_physicalEntrance_data (K := K) ha
  have hCpos : 0 < C := by linarith only [hC]
  let δ := min δ₀ (min (1 / (2 * C)) (referenceCoreWallFloor K / C))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₀ (lt_min (by positivity) (div_pos (referenceCoreWallFloor_pos K) hCpos))
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro k hk v hv x hc hx T X Y
  let z := fromProjectiveState (referenceEntranceState k v)
  let d := normalizedEuclideanDistance z x
  have hd : d ≤ δ := hx
  have hd₀ : d ≤ δ₀ := hd.trans (min_le_left _ _)
  have hdhalf : C * d ≤ 1 / 2 := by
    have H' : d ≤ (1 / 2) / C := by
      simpa only [div_div] using
        (show d ≤ 1 / (2 * C) from hd.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have HH := (le_div_iff₀ hCpos).mp H'
    nlinarith only [HH]
  have hdwall : C * d ≤ referenceCoreWallFloor K := by
    have H' := (le_div_iff₀ hCpos).mp (hd.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [H']
  obtain ⟨⟨hA, hvalid⟩, hreg, hval, herr⟩ := H k hk v hv x hd₀
  have Hact := physicalEntranceData_actual hc hA hvalid
  have hP : (physicalEntranceData x).2.1 = Y := Hact.2.1
  have hX : (physicalEntranceData x).2.2.1 = X := Hact.2.2.1
  have hv' : 0 < v ∧ v < 1 := ⟨ha.trans_le hv.1, by linarith only [hv.2]⟩
  rw [physicalEntranceData_reference hk.1 hv'] at herr
  let q := referencePulse k (-referenceHalfTime k)
  have hproj : ‖(physicalEntranceData x).2.1 - q‖ ≤ C * d :=
    (norm_fst_le _).trans ((norm_snd_le _).trans herr)
  have hphys : ‖(physicalEntranceData x).2.2.1 - fromProjectiveState q‖ ≤ C * d :=
    (norm_fst_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans herr))
  have hrad : |(physicalEntranceData x).2.2.2 - k| ≤ C * d :=
    (norm_snd_le _).trans ((norm_snd_le _).trans ((norm_snd_le _).trans herr))
  obtain ⟨hmq, hnq⟩ := referenceCore_endpoint_bounds hk
  have hM : |Y 0 - q 0| ≤ C * d := by
    rw [hP] at hproj
    exact (norm_le_pi_norm (Y - q) 0).trans hproj
  have hn : |X 3 - fromProjectiveState q 3| ≤ C * d := by
    rw [hX] at hphys
    exact (norm_le_pi_norm (X - fromProjectiveState q) 3).trans hphys
  have hT : T ≤ C := (le_abs_self T).trans ((norm_fst_le _).trans hval)
  have hM' : 1 < Y 0 := by
    change 2 ≤ q 0 at hmq
    have Hlo := (abs_le.mp hM).1
    linarith only [Hlo, hmq, hdhalf]
  have hn' : referenceCoreWallFloor K ≤ X 3 := by
    change 2 * referenceCoreWallFloor K ≤ fromProjectiveState q 3 at hnq
    have Hlo := (abs_le.mp hn).1
    linarith only [Hlo, hnq, hdwall]
  have hr' : |coreRadius (Y 0) (Y 2) - k| ≤ C * d := by
    change |coreRadius ((physicalEntranceData x).2.1 0) ((physicalEntranceData x).2.1 2) - k| ≤ _ at hrad
    rwa [hP] at hrad
  exact ⟨Hact.1, hT, hP ▸ Hact.2.2.2.1, hM', Hact.2.2.2.2.1, hr', hn',
    Hact.2.2.2.2.2.1, Hact.2.2.2.2.2.2, hreg⟩

end BianchiIX
