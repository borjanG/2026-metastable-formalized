import Metastability.ActiveTiming

/-! Absolutely continuous scalar barriers for terminal no-upward-exit. -/

noncomputable section
open Set Filter MeasureTheory

namespace Metastability.ActiveBarrier

theorem sub_nonneg_of_ae_deriv_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ u ∂volume, u ∈ Ioo a b → 0 ≤ deriv f u) : 0 ≤ f b - f a := by
  have hd' : ∀ᵐ u ∂volume.restrict (Icc a b), 0 ≤ deriv f u := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hd, volume.ae_ne a, volume.ae_ne b] with u hu hua hub hmem
    exact hu ⟨lt_of_le_of_ne hmem.1 (Ne.symm hua), lt_of_le_of_ne hmem.2 hub⟩
  have h := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_const (c := (0 : ℝ))) hf.intervalIntegrable_deriv hd'
  simpa only [intervalIntegral.integral_zero, hf.integral_deriv_eq_sub] using h

theorem exists_first_level_of_end_le {f : ℝ → ℝ} {a b target : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hstart : target < f a) (hend : f b ≤ target) :
    ∃ U ∈ Ioc a b, f U = target ∧ ∀ u ∈ Ico a U, target < f u := by
  let Z : Set ℝ := Icc a b ∩ f ⁻¹' Iic target
  have hZ : IsClosed Z := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  obtain ⟨U, hU⟩ := (isCompact_Icc.of_isClosed_subset hZ inter_subset_left).exists_isLeast
    (show Z.Nonempty from ⟨b, ⟨hab, le_rfl⟩, hend⟩)
  have hUa : a < U := by
    apply lt_of_le_of_ne hU.1.1.1
    intro heq
    have h := hU.1.2
    rw [← heq] at h
    exact (not_le.mpr hstart) h
  have hUb : U ≤ b := hU.1.1.2
  have hvalue : f U = target := by
    obtain ⟨V, hV, hval⟩ := intermediate_value_Icc' hUa.le
      (hc.mono (Icc_subset_Icc_right hUb)) ⟨hU.1.2, hstart.le⟩
    have hUV : U ≤ V := hU.2 ⟨⟨hV.1, hV.2.trans hUb⟩, hval.le⟩
    have heq : V = U := le_antisymm hV.2 hUV
    rwa [heq] at hval
  refine ⟨U, ⟨hUa, hUb⟩, hvalue, ?_⟩
  intro u hu
  by_contra h
  exact (not_le.mpr hu.2) (hU.2 ⟨⟨hu.1, hu.2.le.trans hUb⟩, le_of_not_gt h⟩)

/-- A scalar starting at the upper edge of a nontrivial band cannot cross
downward if its a.e. derivative is nonnegative whenever it lies in that band.
No derivative sign is imposed above the band, and no confinement is assumed. -/
theorem no_downcross_of_ae_deriv_nonneg_on_band {f : ℝ → ℝ} {a b lo R : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hlo : lo < R) (hstart : f a = R)
    (hd : ∀ᵐ u ∂volume, u ∈ Ioo a b → f u ∈ Icc lo R → 0 ≤ deriv f u) :
    ∀ t ∈ Icc a b, R ≤ f t := by
  have hc : ContinuousOn f (Icc a b) := by
    simpa only [uIcc_of_le hab] using hf.continuousOn
  intro t ht
  by_contra hbad
  have htR : f t < R := lt_of_not_ge hbad
  let M := (max lo (f t) + R) / 2
  have hmax : max lo (f t) < R := max_lt hlo htR
  have hMR : M < R := by dsimp [M]; linarith only [hmax]
  have hMt : f t < M := by
    dsimp [M]
    have hm := le_max_right lo (f t)
    linarith only [hm, hmax]
  have hloM : lo < M := by
    dsimp [M]
    have hm := le_max_left lo (f t)
    linarith only [hm, hmax]
  obtain ⟨U, hU, hUM, hbefore⟩ := exists_first_level_of_end_le ht.1
    (hc.mono (Icc_subset_Icc_right ht.2)) (hstart.symm ▸ hMR) hMt.le
  let Z : Set ℝ := Icc a U ∩ f ⁻¹' {R}
  have hZ : IsClosed Z := (hc.mono (Icc_subset_Icc_right (hU.2.trans ht.2))).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_singleton
  obtain ⟨V, hV⟩ := (isCompact_Icc.of_isClosed_subset hZ inter_subset_left).exists_isGreatest
    (show Z.Nonempty from ⟨a, ⟨le_rfl, hU.1.le⟩, hstart⟩)
  have hVU : V < U := by
    apply lt_of_le_of_ne hV.1.1.2
    intro heq
    have hVR : f V = R := hV.1.2
    rw [heq, hUM] at hVR
    exact hMR.ne hVR
  have hband : ∀ u ∈ Ioo V U, f u ∈ Icc lo R := by
    intro u hu
    have hau : a ≤ u := hV.1.1.1.trans hu.1.le
    refine ⟨hloM.le.trans (hbefore u ⟨hau, hu.2⟩).le, ?_⟩
    by_contra hnot
    have hfu : R < f u := lt_of_not_ge hnot
    obtain ⟨W, hW, hWR⟩ := intermediate_value_Icc' hu.2.le
      (hc.mono (Icc_subset_Icc hau (hU.2.trans ht.2)))
      (show R ∈ Icc (f U) (f u) from ⟨hUM ▸ hMR.le, hfu.le⟩)
    have hWV : W ≤ V := hV.2 ⟨⟨hau.trans hW.1, hW.2⟩, hWR⟩
    exact (not_le.mpr hu.1) (hW.1.trans hWV)
  have hfVU : AbsolutelyContinuousOnInterval f V U := hf.mono (by
    rw [uIcc_of_le hVU.le, uIcc_of_le hab]
    exact Icc_subset_Icc hV.1.1.1 (hU.2.trans ht.2))
  have hnonneg := sub_nonneg_of_ae_deriv_nonneg hVU.le hfVU (by
    filter_upwards [hd] with u hu humem
    exact hu ⟨hV.1.1.1.trans_lt humem.1, humem.2.trans_le (hU.2.trans ht.2)⟩
      (hband u humem))
  have hVR : f V = R := hV.1.2
  rw [hVR, hUM] at hnonneg
  linarith only [hMR, hnonneg]

end Metastability.ActiveBarrier
