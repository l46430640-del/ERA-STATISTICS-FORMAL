import BianchiIX.Dynamics.EntranceMultiplierColumns
import BianchiIX.Analysis.FiniteLinearWeights

noncomputable section

namespace BianchiIX

def entranceStrongResponseWeight (y d : ProjectiveState) : ℝ :=
  (-Real.log (y 2)) * |d 0| + |d 1| + coreRadius (y 0) (y 2) / y 2 * |d 2| + |d 3|

def entranceWeakResponseWeight (y d : ProjectiveState) : ℝ :=
  ((-Real.log (y 2)) * |d 0| + |d 1| + |d 3|) / coreRadius (y 0) (y 2) ^ 2 + |d 2| / y 2

theorem entranceResponseWeights_nonneg {y : ProjectiveState}
    (hv : 0 < y 2 ∧ y 2 < 1) (d : ProjectiveState) :
    0 ≤ entranceStrongResponseWeight y d ∧ 0 ≤ entranceWeakResponseWeight y d := by
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hk : 0 ≤ coreRadius (y 0) (y 2) := Real.sqrt_nonneg _
  constructor <;> dsimp only [entranceStrongResponseWeight, entranceWeakResponseWeight] <;> positivity [hv.1]

theorem exists_entrance_logMultiplier_weighted_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      7 / 4 ≤ coreRadius (y 0) (y 2) → 1 ≤ y 0 → (0 ≤ y 1 ∧ y 1 ≤ ε) →
      (0 < y 2 ∧ y 2 < 1) → (0 ≤ y 3 ∧ y 3 ≤ ε) → ∀ d : ProjectiveState,
      |entranceLogMultiplierResponse y 0 d| ≤ C * entranceStrongResponseWeight y d ∧
      |entranceLogMultiplierResponse y 2 d| ≤ C * entranceWeakResponseWeight y d := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_logMultiplier_columns_nonneg
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y hk hm hu hv hw d
  obtain ⟨HU, HW⟩ := HC y hk hm hu hv hw
  let k := coreRadius (y 0) (y 2)
  have hs (i : Fin 4) : ‖entranceLogMultiplierResponse y 0 (Pi.single i 1)‖ ≤
      (![C * (-Real.log (y 2)), C, C * k / y 2, C] : Fin 4 → ℝ) i := by
    fin_cases i
    · exact HU.1
    · exact HU.2.1
    · exact HU.2.2.1
    · exact HU.2.2.2
  have hw' (i : Fin 4) : ‖entranceLogMultiplierResponse y 2 (Pi.single i 1)‖ ≤
      (![C * (-Real.log (y 2)) / k ^ 2, C / k ^ 2, C / y 2, C / k ^ 2] : Fin 4 → ℝ) i := by
    fin_cases i
    · exact HW.1
    · exact HW.2.1
    · exact HW.2.2.1
    · exact HW.2.2.2
  constructor
  · have H := clm_norm_le_weighted_coordinates (entranceLogMultiplierResponse y 0) d _ hs
    simp [Fin.sum_univ_four] at H
    convert! H using 1
    unfold entranceStrongResponseWeight k
    ring
  · have H := clm_norm_le_weighted_coordinates (entranceLogMultiplierResponse y 2) d _ hw'
    simp [Fin.sum_univ_four] at H
    convert! H using 1
    unfold entranceWeakResponseWeight k
    ring

theorem EntranceRadialInverseAt.logMultiplier_differential {y : ProjectiveState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (i : Fin 3) (d : ProjectiveState) :
    fderiv ℝ (fun z => Real.log (entranceReturnMultiplier (Ψ z) i)) (entranceRadialCoordinates y) d =
      entranceLogMultiplierResponse y i d :=
  HΨ.scalar_differential ((entranceReturnMultiplier_regular hk hm hu hv hw i).2.1.differentiableAt
    (by norm_num)) d

end BianchiIX
