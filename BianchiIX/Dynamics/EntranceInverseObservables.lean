import BianchiIX.Dynamics.EntranceRadialInverse

noncomputable section

namespace BianchiIX

theorem EntranceRadialInverseAt.observable_fderiv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ProjectiveState} {Ψ Φ : ProjectiveState → ProjectiveState}
    (HΨ : EntranceRadialInverseAt y Ψ) (HΦ : EntranceRadialInverseAt y Φ) (f : ProjectiveState → E) :
    fderiv ℝ (fun z => f (Ψ z)) (entranceRadialCoordinates y) =
      fderiv ℝ (fun z => f (Φ z)) (entranceRadialCoordinates y) := by
  exact ((HΨ.unique HΦ).fun_comp f).fderiv_eq

end BianchiIX
