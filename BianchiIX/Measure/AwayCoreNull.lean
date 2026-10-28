import BianchiIX.Statistics.AwayEraHistories
import BianchiIX.Measure.CompactCoreNull

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Core-curve parameters whose exact future orbit avoids every Taub point by a fixed distance. -/
def curveTaubAvoidance (Γ : EraCurve) (ε : ℝ) : Set ℝ :=
  {x | x ∈ Ioo (0 : ℝ) 1 ∧
    normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry (Γ.state (2 / x))))}

/-- Small positive-wall core coordinates with uniform physical Taub avoidance. -/
def coreTaubAvoidance (ε B : ℝ) : Set CoreAngleState :=
  {q | q 0 ∈ Ioo (0 : ℝ) 1 ∧ 0 < q 1 ∧ 0 < q 2 ∧ q 1 + q 2 ≤ B ∧
    normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2]))}

/-- For each fixed positive Taub distance, avoiding small physical cores form a null set. -/
theorem exists_taubAvoidingCore_null (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Bstar > (0 : ℝ), ∀ B ∈ Ioc 0 Bstar,
      (∀ Γ : EraCurve, Γ.Admissible B → volume (curveTaubAvoidance Γ ε) = 0) ∧
      volume (coreTaubAvoidance ε B) = 0 := by
  obtain ⟨δh, hδh, _, HH⟩ := exists_compactEraHistories_of_taub_avoidance
  obtain ⟨δn, hδn, _, HN⟩ := exists_compactEra_null hBirkhoff
  let η := min δh δn / 2
  have hη : 0 < η := div_pos (lt_min hδh hδn) (by norm_num)
  have hηh : η ≤ δh := by dsimp [η]; linarith only [min_le_left δh δn, hδh]
  have hηn : η ≤ δn := by dsimp [η]; linarith only [min_le_right δh δn, hδn]
  obtain ⟨N, γ, hγ, hγmax, Bh, hBh, _, Hh⟩ :=
    HH η hη hηh 20 (by omega) (1 / 100) (by norm_num) (by norm_num) (by norm_num) ε hε
  obtain ⟨Bcap, _, _, Hn⟩ :=
    HN η hη hηn 20 (by omega) (1 / 100) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Bn, hBn, _, Hnull⟩ := Hn N γ hγ hγmax
  refine ⟨min Bh Bn, lt_min hBh hBn, ?_⟩
  intro B hB
  have hBh' : B ∈ Ioc 0 Bh := ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  obtain ⟨Hcurve, Hcore⟩ := Hnull B ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
  constructor
  · intro Γ hΓ
    apply measure_mono_null (t := curveCompactEraHistories Γ η 20 (1 / 100) B Bcap N γ) _ (Hcurve Γ hΓ)
    intro x hx
    have hr : 2 < 2 / x := (lt_div_iff₀ hx.1.1).mpr (by linarith only [hx.1.2])
    obtain ⟨hu, hw, hsum, _⟩ := hΓ (2 / x) hr
    exact ⟨hx.1, Hh Bcap (B, Γ.state (2 / x)) hBh'
      (by change 2 - γ / 2 ≤ 2 / x; linarith only [hr, hγ]) hu hw hsum hx.2⟩
  · apply measure_mono_null (t := coreCompactEraHistories η 20 (1 / 100) B Bcap N γ) _ Hcore
    intro q hq
    have hr : 2 < 2 / q 0 := (lt_div_iff₀ hq.1.1).mpr (by linarith only [hq.1.2])
    exact ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1,
      Hh Bcap (B, ![2 / q 0, q 1, q 2]) hBh'
        (by change 2 - γ / 2 ≤ 2 / q 0; linarith only [hr, hγ])
        hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2⟩

end BianchiIX
