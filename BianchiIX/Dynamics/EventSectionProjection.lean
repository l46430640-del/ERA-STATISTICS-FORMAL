import BianchiIX.Dynamics.EntranceReturnTransport

noncomputable section

namespace BianchiIX

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Projection onto the section tangent space along the flow direction. -/
def sectionEventProjection (ℓ : E →L[ℝ] ℝ) (v : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ((ℓ v)⁻¹ • ℓ).smulRight v

theorem sectionEventProjection_field (ℓ : E →L[ℝ] ℝ) (v : E) (h : ℓ v ≠ 0) :
    sectionEventProjection ℓ v v = 0 := by
  simp [sectionEventProjection, h]

theorem sectionEventProjection_tangent (ℓ : E →L[ℝ] ℝ) (v w : E) (h : ℓ v ≠ 0) :
    ℓ (sectionEventProjection ℓ v w) = 0 := by
  simp [sectionEventProjection, h, mul_comm]

/-- Every nonzero time rescaling gives exactly the same section projection. -/
theorem sectionEventProjection_rescale (ℓ : E →L[ℝ] ℝ) (v : E) {c : ℝ} (hc : c ≠ 0) :
    sectionEventProjection ℓ (c • v) = sectionEventProjection ℓ v := by
  ext w
  simp [sectionEventProjection, hc, smul_smul, mul_comm, mul_left_comm]

/-- The existing exact event differential is the section projection of the fixed-time flow differential. -/
theorem normalizedEventDifferential_projection (g : NormalizedState → ℝ)
    (x : NormalizedState) (t₀ t : ℝ) :
    normalizedEventDifferential g x t₀ t =
      (sectionEventProjection (fderiv ℝ g (normalizedMaxCurve x t₀ t))
        (normalizedField (normalizedMaxCurve x t₀ t))).comp (normalizedFlowDifferential x t₀ t) := by
  ext w
  simp [normalizedEventDifferential, normalizedEventTimeDifferential, normalizedEventRate,
    sectionEventProjection, sub_eq_add_neg, neg_smul]

end BianchiIX
