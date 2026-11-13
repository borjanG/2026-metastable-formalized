import Metastability.ActiveLogCoordinate
import Metastability.ActiveTimingScales
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Conditional scalar timing with proved finite first hits

The scalar differential estimates in this file are explicit hypotheses.
Absolute continuity is retained, so integration of almost-everywhere bounds
is justified. First hits are produced on finite horizons; their existence is
never assumed and no infimum of an empty real set is used.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Metastability.ActiveTiming

theorem linear_bounds_of_ae_deriv {f : ℝ → ℝ} {a b lower upper : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ u ∂volume, u ∈ Ioo a b → lower ≤ deriv f u ∧ deriv f u ≤ upper) :
    lower * (b - a) ≤ f b - f a ∧ f b - f a ≤ upper * (b - a) := by
  have hd' : ∀ᵐ u ∂volume.restrict (Icc a b), lower ≤ deriv f u ∧ deriv f u ≤ upper := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hd, volume.ae_ne a, volume.ae_ne b] with u hu hua hub hmem
    exact hu ⟨lt_of_le_of_ne hmem.1 (Ne.symm hua), lt_of_le_of_ne hmem.2 hub⟩
  have hlo := intervalIntegral.integral_mono_ae_restrict hab
    (intervalIntegrable_const (c := lower)) hf.intervalIntegrable_deriv (hd'.mono fun _ h => h.1)
  have hhi := intervalIntegral.integral_mono_ae_restrict hab hf.intervalIntegrable_deriv
    (intervalIntegrable_const (c := upper)) (hd'.mono fun _ h => h.2)
  rw [hf.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at hlo hhi
  constructor <;> nlinarith only [hlo, hhi]

theorem sub_le_of_ae_deriv_le {f : ℝ → ℝ} {a b upper : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ u ∂volume, u ∈ Ioo a b → deriv f u ≤ upper) :
    f b - f a ≤ upper * (b - a) := by
  have hd' : ∀ᵐ u ∂volume.restrict (Icc a b), deriv f u ≤ upper := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hd, volume.ae_ne a, volume.ae_ne b] with u hu hua hub hmem
    exact hu ⟨lt_of_le_of_ne hmem.1 (Ne.symm hua), lt_of_le_of_ne hmem.2 hub⟩
  have hhi := intervalIntegral.integral_mono_ae_restrict hab hf.intervalIntegrable_deriv
    (intervalIntegrable_const (c := upper)) hd'
  rw [hf.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at hhi
  nlinarith only [hhi]

/-- A decreasing scalar reaches its target on a sufficiently long finite
horizon. The derivative bound is required only while no earlier hit occurred. -/
theorem exists_first_hit_of_ae_decrease {f : ℝ → ℝ} {a b target rate : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hstart : target < f a)
    (hbudget : f a - target ≤ rate * (b - a))
    (hd : ∀ᵐ u ∂volume, u ∈ Ioo a b →
      (∀ s ∈ Icc a u, target < f s) → deriv f u ≤ -rate) :
    ∃ U ∈ Ioc a b, f U = target ∧ ∀ u ∈ Ico a U, target < f u := by
  have hc : ContinuousOn f (Icc a b) := by
    simpa only [uIcc_of_le hab] using hf.continuousOn
  let Z : Set ℝ := Icc a b ∩ f ⁻¹' Iic target
  have hZ : IsClosed Z := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hZne : Z.Nonempty := by
    by_contra hno
    have habove : ∀ u ∈ Icc a b, target < f u := by
      intro u hu
      by_contra h
      exact hno ⟨u, hu, le_of_not_gt h⟩
    have hdec := sub_le_of_ae_deriv_le hab hf (by
      filter_upwards [hd] with u hu hmem
      exact hu hmem (fun s hs => habove s ⟨hs.1, hs.2.trans hmem.2.le⟩))
    have hend := habove b ⟨hab, le_rfl⟩
    nlinarith only [hbudget, hdec, hend]
  obtain ⟨U, hU⟩ := (isCompact_Icc.of_isClosed_subset hZ inter_subset_left).exists_isLeast hZne
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
  have hUu := hU.2 ⟨⟨hu.1, hu.2.le.trans hUb⟩, le_of_not_gt h⟩
  exact (not_le.mpr hu.2) hUu

/-- Integration of an almost-everywhere additive slope error, including both
closed endpoints. -/
theorem integrated_slope_error {f : ℝ → ℝ} {a b speed error : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ u ∂volume, u ∈ Ioo a b → |deriv f u + speed| ≤ error) :
    |f b - f a + speed * (b - a)| ≤ error * (b - a) := by
  have hbounds := linear_bounds_of_ae_deriv hab hf (lower := -speed - error)
    (upper := -speed + error) (by
      filter_upwards [hd] with u hu hmem
      have h := abs_le.mp (hu hmem)
      constructor <;> linarith only [h.1, h.2])
  apply abs_le.mpr
  constructor <;> nlinarith only [hbounds.1, hbounds.2]

/-- A perturbation of the constant logarithmic slope has an actual finite
first hit and a quantitative duration error. The starting-to-target distance
is within `E` of `L/2`; later applications take `L = log β`. -/
theorem exists_first_hit_with_timing_error {f : ℝ → ℝ} {a target c L δ E : ℝ}
    (hc : 0 < c) (hL : 0 < L) (hδ : 0 ≤ δ)
    (hδsmall : δ ≤ c * L / 2) (hEsmall : E ≤ L / 2)
    (hf : AbsolutelyContinuousOnInterval f a (a + 2 / c))
    (hstart : target < f a) (hgap : |f a - target - L / 2| ≤ E)
    (hd : ∀ᵐ u ∂volume, u ∈ Ioo a (a + 2 / c) →
      (∀ s ∈ Icc a u, target < f s) → |deriv f u + c * L| ≤ δ) :
    ∃ U ∈ Ioc a (a + 2 / c), f U = target ∧
      (∀ u ∈ Ico a U, target < f u) ∧
      |U - a - 1 / (2 * c)| ≤ 2 * δ / (c ^ 2 * L) + E / (c * L) := by
  have hH : a ≤ a + 2 / c := le_add_of_nonneg_right (by positivity)
  have hCL : 0 < c * L := mul_pos hc hL
  have hbudget : f a - target ≤ (c * L / 2) * (a + 2 / c - a) := by
    have heq : (c * L / 2) * (a + 2 / c - a) = L := by field_simp; ring
    rw [heq]
    have h := (abs_le.mp hgap).2
    linarith only [h, hEsmall]
  obtain ⟨U, hU, hvalue, hbefore⟩ := exists_first_hit_of_ae_decrease hH hf hstart hbudget (by
    filter_upwards [hd] with u hu hmem hprefix
    have h := (abs_le.mp (hu hmem hprefix)).2
    linarith only [h, hδsmall])
  have hacU : AbsolutelyContinuousOnInterval f a U := hf.mono (by
    rw [uIcc_of_le hU.1.le, uIcc_of_le hH]
    exact Icc_subset_Icc_right hU.2)
  have herr := integrated_slope_error hU.1.le hacU (speed := c * L) (error := δ) (by
    filter_upwards [hd] with u hu hmem
    exact hu ⟨hmem.1, hmem.2.trans_le hU.2⟩
      (fun s hs => hbefore s ⟨hs.1, hs.2.trans_lt hmem.2⟩))
  rw [hvalue] at herr
  have herr' : |c * L * (U - a) - (f a - target)| ≤ δ * (U - a) := by
    simpa only [show target - f a + c * L * (U - a) =
      c * L * (U - a) - (f a - target) by ring] using herr
  have hsum : |c * L * (U - a) - L / 2| ≤ δ * (U - a) + E := by
    calc
      _ = |(c * L * (U - a) - (f a - target)) + (f a - target - L / 2)| := by ring_nf
      _ ≤ |c * L * (U - a) - (f a - target)| + |f a - target - L / 2| := abs_add_le _ _
      _ ≤ _ := add_le_add herr' hgap
  have hduration : δ * (U - a) ≤ δ * (2 / c) :=
    mul_le_mul_of_nonneg_left (by linarith only [hU.2]) hδ
  refine ⟨U, hU, hvalue, hbefore, ?_⟩
  have heq : (U - a - 1 / (2 * c)) * (c * L) = c * L * (U - a) - L / 2 := by
    field_simp
  have hrhs : (2 * δ / (c ^ 2 * L) + E / (c * L)) * (c * L) = δ * (2 / c) + E := by
    field_simp
  apply (mul_le_mul_iff_left₀ hCL).mp
  calc
    |U - a - 1 / (2 * c)| * (c * L) = |(U - a - 1 / (2 * c)) * (c * L)| := by
      rw [abs_mul, abs_of_pos hCL]
    _ = |c * L * (U - a) - L / 2| := congrArg abs heq
    _ ≤ δ * (2 / c) + E := hsum.trans (add_le_add hduration le_rfl)
    _ = _ := hrhs.symm

/-- The source mesoscopic target gives the real-temperature timing error
`O(log log β / log β)`. This is a conditional scalar theorem: the actual
trajectory must supply absolute continuity and the displayed stopped law. -/
theorem eventual_mesoscopic_timing (c B D : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ β : ℝ in atTop, 1 < β ∧
      ∀ (a : ℝ) (f : ℝ → ℝ), AbsolutelyContinuousOnInterval f a (a + 2 / c) →
      |f a| ≤ B →
      (∀ᵐ u ∂volume, u ∈ Ioo a (a + 2 / c) →
        (∀ s ∈ Icc a u, ActiveTimingScales.angleLog (ActiveScales.mesoscopicScale β) < f s) →
        |deriv f u + c * Real.log β| ≤ D * β ^ (-(1 : ℝ) / 3) * Real.log β) →
      ∃ U ∈ Ioc a (a + 2 / c),
        f U = ActiveTimingScales.angleLog (ActiveScales.mesoscopicScale β) ∧
        (∀ u ∈ Ico a U, ActiveTimingScales.angleLog (ActiveScales.mesoscopicScale β) < f u) ∧
        |U - a - 1 / (2 * c)| ≤ K * (Real.log (Real.log β) / Real.log β) := by
  let K : ℝ := 2 * D / c ^ 2 + (B + 2) / c + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  filter_upwards [ActiveTimingScales.eventually_timing_smallness c B D hc]
    with β hparam
  obtain ⟨hβ, hloglog, hmeso, hδ, hE, hpower⟩ := hparam
  have hlog : 0 < Real.log β := Real.log_pos hβ
  have hratio : 0 ≤ Real.log (Real.log β) / Real.log β := by positivity
  refine ⟨hβ, ?_⟩
  intro a f hf hstart hd
  have htarget := ActiveTimingScales.mesoscopic_log_error hβ hmeso hloglog
  have hgap : |f a - ActiveTimingScales.angleLog (ActiveScales.mesoscopicScale β) -
      Real.log β / 2| ≤ (B + 2) * Real.log (Real.log β) := by
    have hb : B ≤ B * Real.log (Real.log β) := by nlinarith only [hB, hloglog]
    calc
      _ = |f a - (ActiveTimingScales.angleLog (ActiveScales.mesoscopicScale β) + Real.log β / 2)| := by ring_nf
      _ ≤ |f a| + |ActiveTimingScales.angleLog (ActiveScales.mesoscopicScale β) + Real.log β / 2| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f a)
          (-(ActiveTimingScales.angleLog (ActiveScales.mesoscopicScale β) + Real.log β / 2))
      _ ≤ B + 2 * Real.log (Real.log β) := add_le_add hstart htarget
      _ ≤ _ := by nlinarith only [hb]
  have hstart' : ActiveTimingScales.angleLog (ActiveScales.mesoscopicScale β) < f a := by
    have h := (abs_le.mp hgap).1
    linarith only [h, hE, hlog]
  obtain ⟨U, hU, hhit, hbefore, herr⟩ := exists_first_hit_with_timing_error hc hlog
    (by positivity : 0 ≤ D * β ^ (-(1 : ℝ) / 3) * Real.log β)
    (by nlinarith only [mul_le_mul_of_nonneg_right hδ hlog.le])
    (by linarith only [hE, hlog] : (B + 2) * Real.log (Real.log β) ≤ Real.log β / 2)
    hf hstart' hgap hd
  refine ⟨U, hU, hhit, hbefore, herr.trans ?_⟩
  have heq : 2 * (D * β ^ (-(1 : ℝ) / 3) * Real.log β) / (c ^ 2 * Real.log β) +
      ((B + 2) * Real.log (Real.log β)) / (c * Real.log β) =
      (2 * D / c ^ 2) * β ^ (-(1 : ℝ) / 3) +
        ((B + 2) / c) * (Real.log (Real.log β) / Real.log β) := by
    field_simp
  rw [heq]
  have hp := mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 2 * D / c ^ 2)
  dsimp [K]
  nlinarith only [hp, hratio]

end Metastability.ActiveTiming
