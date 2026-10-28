import BianchiIX.Algebra.ExitCycleBoundary

noncomputable section

namespace BianchiIX

def exitSingleBase (R v : ℝ) : ℝ := (2 - exitTailGap R v) ^ 2 + v ^ 2

def exitSingleDefect (u v w : ℝ) : ℝ := (u - w) ^ 2 - 2 * v * (u + w)

def exitSingleError (R u v w : ℝ) : ℝ :=
  exitSingleDefect u v w * (1 + (R ^ 2 - 4 + exitSingleDefect u v w) / exitSingleBase R v)

def exitSinglePhase (R u v w : ℝ) : ℝ := (Real.sqrt (R ^ 2 + exitSingleError R u v w) - 2) / 2

theorem exitSinglePhase_zero {R : ℝ} (hR : 0 ≤ R) (v : ℝ) :
    exitSinglePhase R 0 v 0 = (R - 2) / 2 := by
  simp [exitSinglePhase, exitSingleError, exitSingleDefect, Real.sqrt_sq hR]

theorem exitSingleBase_eq (R v : ℝ) :
    exitSingleBase R v = axisCycleDenom (1 - exitTailGap R v) 0 v 0 := by
  dsimp only [exitSingleBase, axisCycleDenom, curvature]
  ring

theorem exitSingleDenom_eq (R u v w : ℝ) :
    axisCycleDenom (1 - exitTailGap R v) u v w = exitSingleBase R v + exitSingleDefect u v w := by
  rw [axisCycleDenom_wall_split]
  dsimp only [exitSingleBase, exitSingleDefect]
  ring

theorem exitSingleNumerator_eq {R v : ℝ} (hv : v ^ 2 ≤ R ^ 2) (u w : ℝ) :
    exitSingleBase R v + exitSingleDefect u v w - 4 * (2 - exitTailGap R v) =
      R ^ 2 - 4 + exitSingleDefect u v w := by
  have H := exitTailGap_sq hv
  dsimp only [exitSingleBase]
  nlinarith only [H]

/-- The factorization (C.3) is equivalent to the cyclic expression for Xi squared in (C.2). -/
theorem exitSingleSquare_eq {R v : ℝ} (hH : exitSingleBase R v ≠ 0) (u w : ℝ) :
    R ^ 2 + exitSingleError R u v w =
      4 + (exitSingleBase R v + exitSingleDefect u v w) *
        (R ^ 2 - 4 + exitSingleDefect u v w) / exitSingleBase R v := by
  dsimp only [exitSingleError]
  field_simp
  ring

theorem singleStrongPhase_of_invariant {m u X : ℝ} (hX : 2 < X)
    (hI : singleStrongInvariant m u = 2 + 16 / (X ^ 2 - 4)) :
    singleStrongPhase m u = (X - 2) / 2 := by
  have hXm : 0 < X - 2 := sub_pos.mpr hX
  have hXsq : 0 < X ^ 2 - 4 := by nlinarith only [hX]
  have Hq : singleStrongUpperRoot (singleStrongInvariant m u) = (X + 2) / (X - 2) := by
    symm
    apply singleStrongUpperRoot_unique
      (by rw [hI]; linarith only [div_pos (by norm_num : (0 : ℝ) < 16) hXsq])
      ((lt_div_iff₀ hXm).mpr (by linarith only [hX]))
    rw [hI]
    field_simp
    ring
  rw [singleStrongPhase, Hq]
  field_simp
  ring

/-- The explicit terminal phase is the single-strong-wall phase of the actual cyclic coordinates. -/
theorem exitSinglePhase_eq_singleStrongPhase {R u v w : ℝ}
    (hv : v ^ 2 ≤ R ^ 2) (hH₀ : 0 < exitSingleBase R v)
    (hH : 0 < exitSingleBase R v + exitSingleDefect u v w)
    (hN : 0 < R ^ 2 - 4 + exitSingleDefect u v w) :
    let H := axisCycleDenom (1 - exitTailGap R v) u v w
    exitSinglePhase R u v w = singleStrongPhase (1 - 4 * (2 - exitTailGap R v) / H) (4 * v / H) := by
  intro H
  let N := R ^ 2 - 4 + exitSingleDefect u v w
  have hHpos : 0 < H := by dsimp only [H]; rwa [exitSingleDenom_eq]
  have hNpos : 0 < N := hN
  have hNeq : N = H - 4 * (2 - exitTailGap R v) := by
    dsimp only [N, H]
    rw [exitSingleDenom_eq]
    exact (exitSingleNumerator_eq hv u w).symm
  have hm : 1 - 4 * (2 - exitTailGap R v) / H = N / H := by
    rw [hNeq]
    field_simp
  have HI : singleStrongInvariant (1 - 4 * (2 - exitTailGap R v) / H) (4 * v / H) =
      2 + 16 * exitSingleBase R v / (H * N) := by
    rw [hm, singleStrongInvariant]
    have Hpoly : H ^ 2 + N ^ 2 + 16 * v ^ 2 = 2 * H * N + 16 * exitSingleBase R v := by
      rw [hNeq]
      dsimp only [exitSingleBase]
      ring
    field_simp
    nlinarith only [Hpoly]
  let X := Real.sqrt (R ^ 2 + exitSingleError R u v w)
  have HX : R ^ 2 + exitSingleError R u v w = 4 + H * N / exitSingleBase R v := by
    rw [exitSingleSquare_eq hH₀.ne' u w]
    dsimp only [H, N]
    rw [exitSingleDenom_eq]
  have Hpos : 4 < R ^ 2 + exitSingleError R u v w := by
    rw [HX]
    linarith only [div_pos (mul_pos hHpos hNpos) hH₀]
  have hX : 2 < X := (Real.lt_sqrt (by norm_num)).mpr (by norm_num at Hpos ⊢; exact Hpos)
  have hXsq : X ^ 2 = 4 + H * N / exitSingleBase R v := by
    rw [Real.sq_sqrt (by linarith only [Hpos])]
    exact HX
  have HIX : singleStrongInvariant (1 - 4 * (2 - exitTailGap R v) / H) (4 * v / H) =
      2 + 16 / (X ^ 2 - 4) := by
    rw [HI, hXsq]
    field_simp
    ring
  exact (singleStrongPhase_of_invariant hX HIX).symm

end BianchiIX
