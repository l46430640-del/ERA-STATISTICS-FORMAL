import BianchiIX.Algebra.Flow

/-! Projective vector field and exact core energy, Sections 1.2 and A.2. -/

namespace BianchiIX

noncomputable section

def coupling (u v w : ℝ) : ℝ := u * (v + w - u)
def phaseVelocity (m u v w : ℝ) : ℝ :=
  -v ^ 2 + w ^ 2 + u * (v - w) - m * coupling u v w
def strongVelocity (m u v w : ℝ) : ℝ :=
  (1 - m ^ 2 - (v - w) ^ 2 + u ^ 2) * u / 2
def activeVelocity (m u v w : ℝ) : ℝ := (m - 1 - coupling u v w) * v
def weakVelocity (m u v w : ℝ) : ℝ := (-m - 1 - coupling u v w) * w
def coreEnergy (m v : ℝ) : ℝ := (m - 1) ^ 2 + v ^ 2

theorem phaseVelocity_factor (m u v w : ℝ) :
    phaseVelocity m u v w = -(v + w - u) * (v - w + m * u) := by
  unfold phaseVelocity coupling
  ring

theorem weak_product_directional (m u v w : ℝ) :
    activeVelocity m u v w * w + v * weakVelocity m u v w =
      -2 * (1 + coupling u v w) * (v * w) := by
  unfold activeVelocity weakVelocity
  ring

theorem core_energy_directional (m u v w : ℝ) :
    2 * (m - 1) * phaseVelocity m u v w + 2 * v * activeVelocity m u v w =
      -2 * coupling u v w * coreEnergy m v + 2 * (m - 1) * (u - w) ^ 2 := by
  unfold phaseVelocity activeVelocity coreEnergy coupling
  ring

theorem hasDerivAt_core_energy
    {m u v w : ℝ → ℝ} {t : ℝ}
    (hm : HasDerivAt m (phaseVelocity (m t) (u t) (v t) (w t)) t)
    (hv : HasDerivAt v (activeVelocity (m t) (u t) (v t) (w t)) t) :
    HasDerivAt (fun x => coreEnergy (m x) (v x))
      (-2 * coupling (u t) (v t) (w t) * coreEnergy (m t) (v t) +
        2 * (m t - 1) * (u t - w t) ^ 2) t := by
  convert ((hm.sub_const 1).pow 2).add (hv.pow 2) using 1 <;>
    first | rfl | (norm_num [coreEnergy, phaseVelocity, activeVelocity, coupling]; ring)

theorem projective_reflection (m u v w : ℝ) :
    phaseVelocity (-m) u w v = -phaseVelocity m u v w ∧
    strongVelocity (-m) u w v = strongVelocity m u v w ∧
    activeVelocity (-m) u w v = weakVelocity m u v w ∧
    weakVelocity (-m) u w v = activeVelocity m u v w := by
  unfold phaseVelocity strongVelocity activeVelocity weakVelocity coupling
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end

end BianchiIX
