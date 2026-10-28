import BianchiIX.Algebra.StableResidualBounds

noncomputable section

namespace BianchiIX

def stableResidualCoefficient (i : Fin 4) (y : Fin 2 → ℝ) : ℝ :=
  ![stableResidual4 (y 0), stableResidual3 (y 0),
    stableResidual2 (y 0) (y 1), stableResidual1 (y 0) (y 1)] i

def stableResidualProfile (i : Fin 4) (p : Fin 2 → ℝ) : ℝ :=
  let x := p 0
  let R := phaseNorm 1 (x * p 1)
  ![-2 * (1 - x) * x ^ 2 / (1 - 2 * x) ^ 2,
    2 * (3 - 4 * x) * x ^ 2 / (1 - 2 * x) ^ 2,
    -x * ((1 - x) ^ 2 + x ^ 2) / (1 - 2 * x) ^ 2 - (1 - x) / (1 - 2 * x) +
      (R + x) / (R * (R + 1)),
    2 * x + 1 - 1 / (R + 1)] i

theorem stableWeakRadius_reciprocal {m w : ℝ} (hm : -1 < m) :
    stableWeakRadius m w = (m + 1) * phaseNorm 1 ((m + 1)⁻¹ * w) := by
  have hL : 0 < m + 1 := by linarith
  have hR : 0 < phaseNorm 1 ((m + 1)⁻¹ * w) := phaseNorm_pos (by norm_num)
  have hsq := phaseNorm_sq 1 ((m + 1)⁻¹ * w)
  have hsq' : ((m + 1) * phaseNorm 1 ((m + 1)⁻¹ * w)) ^ 2 = (m + 1) ^ 2 + w ^ 2 := by
    rw [mul_pow, hsq]
    field_simp
  nlinarith only [hsq', stableWeakRadius_sq m w, stableWeakRadius_pos (w := w) hm,
    mul_pos hL hR]

theorem stableResidualCoefficient_compactification (i : Fin 4) {m w : ℝ} (hm : 1 < m) :
    stableResidualCoefficient i ![m, w] =
      (m + 1)⁻¹ * stableResidualProfile i ![(m + 1)⁻¹, w] := by
  have hL : m + 1 ≠ 0 := by linarith
  have hD : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have hden : 1 - 2 * (m + 1)⁻¹ = (m - 1) / (m + 1) := by field_simp; ring
  have hx : 1 - 2 * (m + 1)⁻¹ ≠ 0 := by
    rw [hden]
    exact div_ne_zero (by linarith) hL
  have hR : phaseNorm 1 ((m + 1)⁻¹ * w) ≠ 0 := ne_of_gt (phaseNorm_pos (by norm_num))
  have hR1 : phaseNorm 1 ((m + 1)⁻¹ * w) + 1 ≠ 0 := by
    have H := phaseNorm_pos (a := (1 : ℝ)) (b := (m + 1)⁻¹ * w) (by norm_num)
    linarith
  fin_cases i <;>
    dsimp [stableResidualCoefficient, stableResidualProfile, stableResidual4,
      stableResidual3, stableResidual2, stableResidual1] <;>
    (try rw [stableWeakRadius_reciprocal (by linarith : -1 < m)]) <;>
    (try rw [hden]) <;>
    field_simp <;> ring

theorem contDiffAt_stableResidualProfile (n : WithTop ℕ∞) (i : Fin 4) {p : Fin 2 → ℝ}
    (hp : p 0 < 1 / 2) : ContDiffAt ℝ n (stableResidualProfile i) p := by
  have hd : 1 - 2 * p 0 ≠ 0 := by linarith
  have hd2 := pow_ne_zero 2 hd
  have hs : (1 : ℝ) ^ 2 + (p 0 * p 1) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hR : phaseNorm 1 (p 0 * p 1) ≠ 0 := ne_of_gt (phaseNorm_pos (by norm_num))
  have hR1 : phaseNorm 1 (p 0 * p 1) + 1 ≠ 0 := by
    have H := phaseNorm_pos (a := (1 : ℝ)) (b := p 0 * p 1) (by norm_num)
    linarith
  dsimp [phaseNorm] at hR hR1
  have hRR := mul_ne_zero hR hR1
  fin_cases i <;> unfold stableResidualProfile <;> dsimp [phaseNorm] <;> fun_prop

end BianchiIX
