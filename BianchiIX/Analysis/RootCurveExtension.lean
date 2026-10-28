import BianchiIX.Analysis.RootExtension

/-! Joining the two root-amplitude tails to a curve without changing its original interval. -/

open Set Filter
open scoped Topology

namespace BianchiIX

noncomputable section

def rootCurveExtension (l r : ℝ) (f df : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < l then rootExtension (f l) (df l) (-1) (x - l)
  else if r < x then rootExtension (f r) (df r) 1 (x - r) else f x

def rootCurveDerivative (l r : ℝ) (f df : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < l then df l * rootCutoff (-(x - l) / f l)
  else if r < x then df r * rootCutoff ((x - r) / f r) else df x

theorem rootCurveExtension_middle {l r x : ℝ} (f df : ℝ → ℝ) (hx : x ∈ Icc l r) :
    rootCurveExtension l r f df x = f x ∧ rootCurveDerivative l r f df x = df x := by
  simp [rootCurveExtension, rootCurveDerivative, not_lt_of_ge hx.1, not_lt_of_ge hx.2]

theorem rootCurveExtension_left {l r x : ℝ} (f df : ℝ → ℝ) (hlr : l ≤ r) (hx : x ≤ l) :
    rootCurveExtension l r f df x = rootExtension (f l) (df l) (-1) (x - l) ∧
      rootCurveDerivative l r f df x = df l * rootCutoff (-(x - l) / f l) := by
  rcases lt_or_eq_of_le hx with hx | rfl
  · simp [rootCurveExtension, rootCurveDerivative, hx]
  · simp [rootCurveExtension, rootCurveDerivative, not_lt_of_ge hlr, rootExtension_zero, rootCutoff]

theorem rootCurveExtension_right {l r x : ℝ} (f df : ℝ → ℝ) (hlr : l ≤ r) (hx : r ≤ x) :
    rootCurveExtension l r f df x = rootExtension (f r) (df r) 1 (x - r) ∧
      rootCurveDerivative l r f df x = df r * rootCutoff ((x - r) / f r) := by
  rcases lt_or_eq_of_le hx with hx | rfl
  · simp [rootCurveExtension, rootCurveDerivative, hx, not_lt_of_ge (hlr.trans hx.le)]
  · simp [rootCurveExtension, rootCurveDerivative, not_lt_of_ge hlr, rootExtension_zero, rootCutoff]

private theorem hasDerivAt_rootExtension_shift {s e : ℝ} (hs : 0 < s) (he : |e| = 1)
    (d c x : ℝ) : HasDerivAt (fun z => rootExtension s d e (z - c))
      (d * rootCutoff (e * (x - c) / s)) x := by
  simpa only [Function.comp_def, id_eq, mul_one] using
    (hasDerivAt_rootExtension hs he d (x - c)).comp x ((hasDerivAt_id x).sub_const c)

theorem hasDerivAt_rootCurveExtension {l r : ℝ} (hlr : l < r) {f df : ℝ → ℝ}
    (hfl : 0 < f l) (hfr : 0 < f r)
    (hf : ∀ x ∈ Icc l r, HasDerivWithinAt f (df x) (Icc l r) x) (x : ℝ) :
    HasDerivAt (rootCurveExtension l r f df) (rootCurveDerivative l r f df x) x := by
  have hL (z : ℝ) : HasDerivAt (fun u => rootExtension (f l) (df l) (-1) (u - l))
      (df l * rootCutoff (-(z - l) / f l)) z := by
    simpa only [neg_mul, one_mul] using
      hasDerivAt_rootExtension_shift (e := -1) hfl (by norm_num) (df l) l z
  have hR (z : ℝ) : HasDerivAt (fun u => rootExtension (f r) (df r) 1 (u - r))
      (df r * rootCutoff ((z - r) / f r)) z := by
    simpa only [one_mul] using hasDerivAt_rootExtension_shift (e := 1) hfr (by norm_num) (df r) r z
  by_cases hxl : x < l
  · rw [(rootCurveExtension_left f df hlr.le hxl.le).2]
    apply (hL x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hxl] with z hz
    exact (rootCurveExtension_left f df hlr.le hz.le).1
  by_cases hrx : r < x
  · rw [(rootCurveExtension_right f df hlr.le hrx.le).2]
    apply (hR x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hrx] with z hz
    exact (rootCurveExtension_right f df hlr.le hz.le).1
  have hx : x ∈ Icc l r := ⟨le_of_not_gt hxl, le_of_not_gt hrx⟩
  rw [(rootCurveExtension_middle f df hx).2]
  have hM := (hf x hx).congr_of_mem (fun z hz => (rootCurveExtension_middle f df hz).1) hx
  rcases hx.1.eq_or_lt with h | hleft
  · subst x
    have htail : HasDerivWithinAt (rootCurveExtension l r f df) (df l) (Iic l) l := by
      have h := hL l
      norm_num [rootCutoff] at h
      exact h.hasDerivWithinAt.congr_of_mem
        (fun z hz => (rootCurveExtension_left f df hlr.le hz).1) self_mem_Iic
    have hu : Iic l ∪ Icc l r = Iic r := by
      ext z
      simp only [mem_union, mem_Iic, mem_Icc]
      constructor
      · rintro (h | h)
        · exact h.trans hlr.le
        · exact h.2
      · intro h
        exact (le_total z l).elim Or.inl (fun hz => Or.inr ⟨hz, h⟩)
    have h := htail.union hM
    rw [hu] at h
    exact h.hasDerivAt (Iic_mem_nhds hlr)
  rcases hx.2.eq_or_lt with h | hright
  · subst x
    have htail : HasDerivWithinAt (rootCurveExtension l r f df) (df r) (Ici r) r := by
      have h := hR r
      norm_num [rootCutoff] at h
      exact h.hasDerivWithinAt.congr_of_mem
        (fun z hz => (rootCurveExtension_right f df hlr.le hz).1) self_mem_Ici
    have hu : Icc l r ∪ Ici r = Ici l := by
      ext z
      simp only [mem_union, mem_Icc, mem_Ici]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact hlr.le.trans h
      · intro h
        exact (le_total z r).elim (fun hz => Or.inl ⟨h, hz⟩) Or.inr
    have h := hM.union htail
    rw [hu] at h
    exact h.hasDerivAt (Ici_mem_nhds hlr)
  exact hM.hasDerivAt (Icc_mem_nhds hleft hright)

theorem continuous_rootCurveDerivative {l r : ℝ} (hlr : l ≤ r) {f df : ℝ → ℝ}
    (hdf : ContinuousOn df (Icc l r)) : Continuous (rootCurveDerivative l r f df) := by
  have hL : ContinuousOn (rootCurveDerivative l r f df) (Iic l) := by
    have hc : Continuous (fun x => df l * rootCutoff (-(x - l) / f l)) :=
      (continuous_rootCutoff.comp ((continuous_id.sub continuous_const).neg.div_const (f l))).const_mul (df l)
    exact hc.continuousOn.congr (fun x hx => (rootCurveExtension_left f df hlr hx).2)
  have hM : ContinuousOn (rootCurveDerivative l r f df) (Icc l r) :=
    hdf.congr (fun x hx => (rootCurveExtension_middle f df hx).2)
  have hR : ContinuousOn (rootCurveDerivative l r f df) (Ici r) := by
    have hc : Continuous (fun x => df r * rootCutoff ((x - r) / f r)) :=
      (continuous_rootCutoff.comp ((continuous_id.sub continuous_const).div_const (f r))).const_mul (df r)
    exact hc.continuousOn.congr (fun x hx => (rootCurveExtension_right f df hlr hx).2)
  have h := (hL.union_of_isClosed hM isClosed_Iic isClosed_Icc).union_of_isClosed hR
    (isClosed_Iic.union isClosed_Icc) isClosed_Ici
  have hu : (Iic l ∪ Icc l r) ∪ Ici r = univ := by
    ext x
    simp only [mem_union, mem_Iic, mem_Icc, mem_Ici, mem_univ, iff_true]
    rcases le_total x l with hx | hx
    · exact Or.inl (Or.inl hx)
    rcases le_total x r with hr | hr
    · exact Or.inl (Or.inr ⟨hx, hr⟩)
    · exact Or.inr hr
  rwa [hu, continuousOn_univ] at h

theorem contDiff_rootCurveExtension {l r : ℝ} (hlr : l < r) {f df : ℝ → ℝ}
    (hfl : 0 < f l) (hfr : 0 < f r)
    (hf : ∀ x ∈ Icc l r, HasDerivWithinAt f (df x) (Icc l r) x)
    (hdf : ContinuousOn df (Icc l r)) : ContDiff ℝ 1 (rootCurveExtension l r f df) := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x => (hasDerivAt_rootCurveExtension hlr hfl hfr hf x).differentiableAt,
    (continuous_rootCurveDerivative hlr.le hdf).congr
      (fun x => (hasDerivAt_rootCurveExtension hlr hfl hfr hf x).deriv.symm)⟩

theorem rootCurveExtension_pos {l r θ : ℝ} (hlr : l ≤ r) {f df : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < f x) (hd : ∀ x ∈ Icc l r, |df x| ≤ θ / 2)
    (hθ : θ ≤ 1) (x : ℝ) : 0 < rootCurveExtension l r f df x := by
  by_cases hxl : x < l
  · rw [(rootCurveExtension_left f df hlr hxl.le).1]
    exact rootExtension_pos (hpos l ⟨le_rfl, hlr⟩) (by norm_num) (by linarith)
      (hd l ⟨le_rfl, hlr⟩) hθ
  by_cases hrx : r < x
  · rw [(rootCurveExtension_right f df hlr hrx.le).1]
    exact rootExtension_pos (hpos r ⟨hlr, le_rfl⟩) (by norm_num) (by linarith)
      (hd r ⟨hlr, le_rfl⟩) hθ
  have hx : x ∈ Icc l r := ⟨le_of_not_gt hxl, le_of_not_gt hrx⟩
  rw [(rootCurveExtension_middle f df hx).1]
  exact hpos x hx

theorem rootCurveDerivative_bound {l r θ : ℝ} (hlr : l ≤ r) {f df : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < f x) (hd : ∀ x ∈ Icc l r, |df x| ≤ θ / 2)
    (x : ℝ) : |rootCurveDerivative l r f df x| ≤ θ / 2 := by
  by_cases hxl : x < l
  · rw [(rootCurveExtension_left f df hlr hxl.le).2]
    simpa only [neg_mul, one_mul] using
      rootExtension_derivative_bound (e := -1) (s := f l) (x := x - l)
        (hpos l ⟨le_rfl, hlr⟩) (by linarith) (hd l ⟨le_rfl, hlr⟩)
  by_cases hrx : r < x
  · rw [(rootCurveExtension_right f df hlr hrx.le).2]
    simpa only [one_mul] using
      rootExtension_derivative_bound (e := 1) (s := f r) (x := x - r)
        (hpos r ⟨hlr, le_rfl⟩) (by linarith) (hd r ⟨hlr, le_rfl⟩)
  have hx : x ∈ Icc l r := ⟨le_of_not_gt hxl, le_of_not_gt hrx⟩
  rw [(rootCurveExtension_middle f df hx).2]
  exact hd x hx

theorem rootCurveExtension_square_cone {l r θ : ℝ} (hlr : l < r) {f df : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < f x) (hd : ∀ x ∈ Icc l r, |df x| ≤ θ / 2) (hθ : θ ≤ 1)
    (hf : ∀ x ∈ Icc l r, HasDerivWithinAt f (df x) (Icc l r) x) (x : ℝ) :
    |deriv (fun z => rootCurveExtension l r f df z ^ 2) x| ≤
      θ * Real.sqrt (rootCurveExtension l r f df x ^ 2) :=
  square_derivative_cone
    (hasDerivAt_rootCurveExtension hlr (hpos l ⟨le_rfl, hlr.le⟩) (hpos r ⟨hlr.le, le_rfl⟩) hf x)
    (rootCurveExtension_pos hlr.le hpos hd hθ x) (rootCurveDerivative_bound hlr.le hpos hd x)

theorem rootCurveExtension_pair_bound_sharp {l r θ B : ℝ} (hlr : l ≤ r) {f g df dg : ℝ → ℝ}
    (hf : ∀ x ∈ Icc l r, 0 < f x) (hg : ∀ x ∈ Icc l r, 0 < g x)
    (hdf : ∀ x ∈ Icc l r, |df x| ≤ θ / 2) (hdg : ∀ x ∈ Icc l r, |dg x| ≤ θ / 2)
    (hθ : θ ≤ 1) (hB : ∀ x ∈ Icc l r, f x ^ 2 + g x ^ 2 ≤ B) (x : ℝ) :
    rootCurveExtension l r f df x ^ 2 + rootCurveExtension l r g dg x ^ 2 ≤ (1 + θ / 4) ^ 2 * B := by
  by_cases hxl : x < l
  · rw [(rootCurveExtension_left f df hlr hxl.le).1, (rootCurveExtension_left g dg hlr hxl.le).1]
    exact rootExtension_pair_bound (hf l ⟨le_rfl, hlr⟩) (hg l ⟨le_rfl, hlr⟩)
      (by norm_num) (by linarith) (hdf l ⟨le_rfl, hlr⟩) (hdg l ⟨le_rfl, hlr⟩) hθ (hB l ⟨le_rfl, hlr⟩)
  by_cases hrx : r < x
  · rw [(rootCurveExtension_right f df hlr hrx.le).1, (rootCurveExtension_right g dg hlr hrx.le).1]
    exact rootExtension_pair_bound (hf r ⟨hlr, le_rfl⟩) (hg r ⟨hlr, le_rfl⟩)
      (by norm_num) (by linarith) (hdf r ⟨hlr, le_rfl⟩) (hdg r ⟨hlr, le_rfl⟩) hθ (hB r ⟨hlr, le_rfl⟩)
  have hx : x ∈ Icc l r := ⟨le_of_not_gt hxl, le_of_not_gt hrx⟩
  rw [(rootCurveExtension_middle f df hx).1, (rootCurveExtension_middle g dg hx).1]
  have h := hB x hx
  have hB0 : 0 ≤ B := (add_nonneg (sq_nonneg (f x)) (sq_nonneg (g x))).trans h
  have hθ0 : 0 ≤ θ := by linarith [hdf x hx, abs_nonneg (df x)]
  have hfactor : 1 ≤ (1 + θ / 4) ^ 2 := by nlinarith
  exact h.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hB0])

theorem rootCurveExtension_pair_bound {l r θ B : ℝ} (hlr : l ≤ r) {f g df dg : ℝ → ℝ}
    (hf : ∀ x ∈ Icc l r, 0 < f x) (hg : ∀ x ∈ Icc l r, 0 < g x)
    (hdf : ∀ x ∈ Icc l r, |df x| ≤ θ / 2) (hdg : ∀ x ∈ Icc l r, |dg x| ≤ θ / 2)
    (hθ : θ ≤ 1) (hB : ∀ x ∈ Icc l r, f x ^ 2 + g x ^ 2 ≤ B) (x : ℝ) :
    rootCurveExtension l r f df x ^ 2 + rootCurveExtension l r g dg x ^ 2 ≤ (25 / 16) * B := by
  have hl : l ∈ Icc l r := ⟨le_rfl, hlr⟩
  have hB0 : 0 ≤ B := (add_nonneg (sq_nonneg (f l)) (sq_nonneg (g l))).trans (hB l hl)
  have hθ0 : 0 ≤ θ := by linarith [hdf l hl, abs_nonneg (df l)]
  have hfactor : (1 + θ / 4) ^ 2 ≤ (25 / 16 : ℝ) := by nlinarith
  exact (rootCurveExtension_pair_bound_sharp hlr hf hg hdf hdg hθ hB x).trans
    (mul_le_mul_of_nonneg_right hfactor hB0)

theorem measurable_rootCurveExtension {X : Type*} [MeasurableSpace X]
    {l r x : X → ℝ} {f df : X → ℝ → ℝ} (hl : Measurable l) (hr : Measurable r) (hx : Measurable x)
    (hfl : Measurable (fun q => f q (l q))) (hfr : Measurable (fun q => f q (r q)))
    (hdl : Measurable (fun q => df q (l q))) (hdr : Measurable (fun q => df q (r q)))
    (hfx : Measurable (fun q => f q (x q))) :
    Measurable (fun q => rootCurveExtension (l q) (r q) (f q) (df q) (x q)) := by
  exact Measurable.ite (measurableSet_lt hx hl)
    (measurable_rootExtension hfl hdl measurable_const (hx.sub hl))
    (Measurable.ite (measurableSet_lt hr hx)
      (measurable_rootExtension hfr hdr measurable_const (hx.sub hr)) hfx)

theorem measurable_rootCurveDerivative {X : Type*} [MeasurableSpace X]
    {l r x : X → ℝ} {f df : X → ℝ → ℝ} (hl : Measurable l) (hr : Measurable r) (hx : Measurable x)
    (hfl : Measurable (fun q => f q (l q))) (hfr : Measurable (fun q => f q (r q)))
    (hdl : Measurable (fun q => df q (l q))) (hdr : Measurable (fun q => df q (r q)))
    (hdx : Measurable (fun q => df q (x q))) :
    Measurable (fun q => rootCurveDerivative (l q) (r q) (f q) (df q) (x q)) := by
  exact Measurable.ite (measurableSet_lt hx hl)
    (hdl.mul (continuous_rootCutoff.measurable.comp ((hx.sub hl).neg.div hfl)))
    (Measurable.ite (measurableSet_lt hr hx)
      (hdr.mul (continuous_rootCutoff.measurable.comp ((hx.sub hr).div hfr))) hdx)

end
end BianchiIX
