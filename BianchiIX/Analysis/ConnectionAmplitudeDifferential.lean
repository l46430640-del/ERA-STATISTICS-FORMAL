import BianchiIX.Analysis.MatchingPhaseWeighted

noncomputable section

namespace BianchiIX

def connectionStrongClockRate (m u v w : ℝ) : ℝ :=
  connectionStrongRate m u v w / connectionSpeed m u v w

def connectionWeakClockRate (m u v w : ℝ) : ℝ :=
  -1 - 2 * (1 + coupling u v w) / connectionSpeed m u v w

theorem hasDerivAt_coupling {u v w : ℝ → ℝ} {u' v' w' t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => coupling (u s) (v s) (w s))
      (u' * (v t + w t - 2 * u t) + u t * (v' + w')) t := by
  convert! hu.mul ((hv.add hw).sub hu) using 1
  dsimp
  ring

theorem hasDerivAt_connectionSpeed {m u v w : ℝ → ℝ} {m' u' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => connectionSpeed (m s) (u s) (v s) (w s))
      (m' - (u' * (v t + w t - 2 * u t) + u t * (v' + w'))) t :=
  (hm.sub_const 1).sub (hasDerivAt_coupling hu hv hw)

theorem hasDerivAt_connectionStrongClockRate {m u v w : ℝ → ℝ} {m' u' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionStrongClockRate (m s) (u s) (v s) (w s))
      ((-m t * m' - (v t - w t) * (v' - w') + u t * u' -
        connectionStrongClockRate (m t) (u t) (v t) (w t) *
          (m' - (u' * (v t + w t - 2 * u t) + u t * (v' + w')))) /
        connectionSpeed (m t) (u t) (v t) (w t)) t := by
  have hN : HasDerivAt (fun s => connectionStrongRate (m s) (u s) (v s) (w s))
      (-m t * m' - (v t - w t) * (v' - w') + u t * u') t := by
    convert! ((((hm.pow 2).const_sub 1).sub ((hv.sub hw).pow 2)).add (hu.pow 2)).div_const 2 using 1
    dsimp
    ring
  apply (hN.div (hasDerivAt_connectionSpeed hm hu hv hw) hD).congr_deriv
  dsimp [connectionStrongClockRate]
  field_simp

theorem hasDerivAt_connectionWeakClockRate {m u v w : ℝ → ℝ} {m' u' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionWeakClockRate (m s) (u s) (v s) (w s))
      ((2 * (1 + coupling (u t) (v t) (w t)) * m' -
        2 * m t * (u' * (v t + w t - 2 * u t) + u t * (v' + w'))) /
        connectionSpeed (m t) (u t) (v t) (w t) ^ 2) t := by
  have H := ((((hasDerivAt_coupling hu hv hw).const_add 1).const_mul 2).div
    (hasDerivAt_connectionSpeed hm hu hv hw) hD).const_sub (-1)
  apply H.congr_deriv
  dsimp [connectionSpeed]
  ring

/-- The four columns are J, log U, log V, log W, with J fixed in the last three. -/
def connectionStrongClockPartials (m u v w : ℝ) : Fin 4 → ℝ :=
  let a := connectionStrongClockRate m u v w
  let D := connectionSpeed m u v w
  ![-(m + a) / (D * matchingPhaseSlope m v w),
    (u ^ 2 + a * u * (v + w - 2 * u)) / D,
    (-(m + a) * matchingPhaseVVariation m v w - v * (v - w) + a * u * v) / D,
    (-(m + a) * matchingPhaseWVariation m v w + w * (v - w) + a * u * w) / D]

def connectionWeakClockPartials (m u v w : ℝ) : Fin 4 → ℝ :=
  let D := connectionSpeed m u v w
  ![2 * (1 + coupling u v w) / (D ^ 2 * matchingPhaseSlope m v w),
    -(2 * m * u * (v + w - 2 * u)) / D ^ 2,
    (2 * (1 + coupling u v w) * matchingPhaseVVariation m v w - 2 * m * u * v) / D ^ 2,
    (2 * (1 + coupling u v w) * matchingPhaseWVariation m v w - 2 * m * u * w) / D ^ 2]

theorem hasDerivAt_connection_clock_weighted_curves {m u v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hu : HasDerivAt u (u t * d 1) t) (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t)
    (hD : connectionSpeed (m t) (u t) (v t) (w t) ≠ 0) :
    HasDerivAt (fun s => connectionStrongClockRate (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionStrongClockPartials (m t) (u t) (v t) (w t) i * d i) t ∧
    HasDerivAt (fun s => connectionWeakClockRate (m s) (u s) (v s) (w s))
      (∑ i : Fin 4, connectionWeakClockPartials (m t) (u t) (v t) (w t) i * d i) t := by
  constructor
  · apply (hasDerivAt_connectionStrongClockRate hm hu hv hw hD).congr_deriv
    simp [Fin.sum_univ_succ, connectionStrongClockPartials]
    ring
  · apply (hasDerivAt_connectionWeakClockRate hm hu hv hw hD).congr_deriv
    simp [Fin.sum_univ_succ, connectionWeakClockPartials]
    ring

end BianchiIX
