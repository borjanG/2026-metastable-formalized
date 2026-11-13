import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Inverting the integral of a bounded positive measurable rate

This module constructs a time change, rather than assuming its existence.
The full real line is used for the construction. The resulting inverse fixes
zero and preserves nonnegativity, so its restriction gives a clock on the
nonnegative half-line. Differentiation of the inverse is proved at every point
where the rate is continuous at the corresponding original time.
-/

noncomputable section

open MeasureTheory Set Filter

namespace Metastability.PositiveClock

/-- Measurability and the two pointwise bounds needed for the integral clock.
These are assumptions on the given rate, not assumptions on a clock. -/
structure BoundedPositiveRate where
  rate : ℝ → ℝ
  measurable_rate : Measurable rate
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  lower_bound : ∀ u, lower ≤ rate u
  upper_bound : ∀ u, rate u ≤ upper

namespace BoundedPositiveRate

variable (r : BoundedPositiveRate)

theorem rate_pos (u : ℝ) : 0 < r.rate u :=
  r.lower_pos.trans_le (r.lower_bound u)

theorem upper_pos : 0 < r.upper :=
  (r.rate_pos 0).trans_le (r.upper_bound 0)

theorem inv_rate_bounds (u : ℝ) :
    r.upper⁻¹ ≤ (r.rate u)⁻¹ ∧ (r.rate u)⁻¹ ≤ r.lower⁻¹ :=
  ⟨inv_anti₀ (r.rate_pos u) (r.upper_bound u),
    inv_anti₀ r.lower_pos (r.lower_bound u)⟩

theorem norm_inv_rate_le (u : ℝ) : ‖(r.rate u)⁻¹‖ ≤ r.lower⁻¹ := by
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (r.rate_pos u).le)]
  exact (r.inv_rate_bounds u).2

theorem intervalIntegrable_inv_rate (a b : ℝ) :
    IntervalIntegrable (fun u => (r.rate u)⁻¹) volume a b := by
  apply (intervalIntegrable_const (c := r.lower⁻¹)).mono_fun'
  · exact r.measurable_rate.inv.aestronglyMeasurable
  · exact Eventually.of_forall r.norm_inv_rate_le

/-- Elapsed accelerated time as a function of original time. -/
def elapsed (u : ℝ) : ℝ := ∫ v in 0..u, (r.rate v)⁻¹

@[simp]
theorem elapsed_zero : r.elapsed 0 = 0 := by
  simp only [elapsed, intervalIntegral.integral_same]

theorem elapsed_sub (a b : ℝ) :
    r.elapsed b - r.elapsed a = ∫ v in a..b, (r.rate v)⁻¹ :=
  intervalIntegral.integral_interval_sub_left
    (r.intervalIntegrable_inv_rate 0 b) (r.intervalIntegrable_inv_rate 0 a)

/-- Quantitative lower and upper bounds on increments of elapsed time. -/
theorem elapsed_increment_bounds (a b : ℝ) (hab : a ≤ b) :
    (b - a) / r.upper ≤ r.elapsed b - r.elapsed a ∧
      r.elapsed b - r.elapsed a ≤ (b - a) / r.lower := by
  rw [r.elapsed_sub]
  constructor
  · have h := intervalIntegral.integral_mono_on hab
      (intervalIntegrable_const (c := r.upper⁻¹))
      (r.intervalIntegrable_inv_rate a b)
      (fun u _ => (r.inv_rate_bounds u).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using h
  · have h := intervalIntegral.integral_mono_on hab
      (r.intervalIntegrable_inv_rate a b)
      (intervalIntegrable_const (c := r.lower⁻¹))
      (fun u _ => (r.inv_rate_bounds u).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv] using h

theorem elapsed_strictMono : StrictMono r.elapsed := by
  intro a b hab
  have h := (r.elapsed_increment_bounds a b hab.le).1
  exact sub_pos.mp ((div_pos (sub_pos.mpr hab) r.upper_pos).trans_le h)

theorem elapsed_dist_le (a b : ℝ) :
    dist (r.elapsed a) (r.elapsed b) ≤ r.lower⁻¹ * dist a b := by
  rw [Real.dist_eq, r.elapsed_sub, Real.dist_eq]
  simpa only [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := b) (b := a) (fun u _ => r.norm_inv_rate_le u)

theorem elapsed_lipschitz : LipschitzWith (Real.toNNReal r.lower⁻¹) r.elapsed :=
  LipschitzWith.of_dist_le' r.elapsed_dist_le

theorem elapsed_continuous : Continuous r.elapsed :=
  r.elapsed_lipschitz.continuous

theorem dist_le_upper_mul_elapsed_dist (a b : ℝ) :
    dist a b ≤ r.upper * dist (r.elapsed a) (r.elapsed b) := by
  have hordered : ∀ a b : ℝ, a ≤ b →
      dist a b ≤ r.upper * dist (r.elapsed a) (r.elapsed b) := by
    intro a b hab
    have h := (div_le_iff₀ r.upper_pos).mp (r.elapsed_increment_bounds a b hab).1
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab),
      Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (r.elapsed_strictMono.monotone hab))]
    linarith only [h]
  rcases le_total a b with hab | hba
  · exact hordered a b hab
  · simpa only [dist_comm b a, dist_comm (r.elapsed b) (r.elapsed a)] using hordered b a hba

theorem elapsed_surjective : Function.Surjective r.elapsed := by
  intro t
  apply mem_range_of_exists_le_of_exists_ge r.elapsed_continuous
  · by_cases ht : 0 ≤ t
    · exact ⟨0, by simpa only [r.elapsed_zero] using ht⟩
    · have ht' : t ≤ 0 := (lt_of_not_ge ht).le
      refine ⟨t * r.upper, ?_⟩
      have h := (r.elapsed_increment_bounds (t * r.upper) 0
        (mul_nonpos_of_nonpos_of_nonneg ht' r.upper_pos.le)).1
      have hdiv : (0 - t * r.upper) / r.upper = -t := by
        rw [zero_sub, neg_div, mul_div_cancel_right₀ t r.upper_pos.ne']
      rw [hdiv, r.elapsed_zero, zero_sub] at h
      exact neg_le_neg_iff.mp h
  · by_cases ht : 0 ≤ t
    · refine ⟨t * r.upper, ?_⟩
      have h := (r.elapsed_increment_bounds 0 (t * r.upper)
        (mul_nonneg ht r.upper_pos.le)).1
      simpa only [sub_zero, r.elapsed_zero,
        mul_div_cancel_right₀ t r.upper_pos.ne'] using h
    · refine ⟨0, ?_⟩
      rw [r.elapsed_zero]
      exact (lt_of_not_ge ht).le

/-- The inverse clock, defined using the proved surjectivity of elapsed time. -/
def clock : ℝ → ℝ := Function.surjInv r.elapsed_surjective

@[simp]
theorem elapsed_clock (t : ℝ) : r.elapsed (r.clock t) = t :=
  Function.surjInv_eq r.elapsed_surjective t

@[simp]
theorem clock_elapsed (u : ℝ) : r.clock (r.elapsed u) = u :=
  Function.leftInverse_surjInv ⟨r.elapsed_strictMono.injective, r.elapsed_surjective⟩ u

@[simp]
theorem clock_zero : r.clock 0 = 0 := by
  simpa only [r.elapsed_zero] using r.clock_elapsed 0

theorem clock_unique (g : ℝ → ℝ) (hg : ∀ t, r.elapsed (g t) = t) : g = r.clock := by
  funext t
  apply r.elapsed_strictMono.injective
  rw [hg, r.elapsed_clock]

theorem clock_dist_le (s t : ℝ) : dist (r.clock s) (r.clock t) ≤ r.upper * dist s t := by
  simpa only [r.elapsed_clock] using r.dist_le_upper_mul_elapsed_dist (r.clock s) (r.clock t)

theorem clock_lipschitz : LipschitzWith (Real.toNNReal r.upper) r.clock :=
  LipschitzWith.of_dist_le' r.clock_dist_le

theorem clock_continuous : Continuous r.clock := r.clock_lipschitz.continuous

theorem clock_strictMono : StrictMono r.clock := by
  intro s t hst
  apply r.elapsed_strictMono.lt_iff_lt.mp
  simpa only [r.elapsed_clock] using hst

theorem clock_nonneg_iff (t : ℝ) : 0 ≤ r.clock t ↔ 0 ≤ t := by
  simpa only [r.clock_zero] using (r.clock_strictMono.le_iff_le (a := 0) (b := t))

/-- The derivative of elapsed time at continuity points of the rate. -/
theorem hasDerivAt_elapsed (u : ℝ) (hu : ContinuousAt r.rate u) :
    HasDerivAt r.elapsed (r.rate u)⁻¹ u := by
  exact intervalIntegral.integral_hasDerivAt_right
    (r.intervalIntegrable_inv_rate 0 u)
    r.measurable_rate.inv.stronglyMeasurable.stronglyMeasurableAtFilter
    (hu.inv₀ (r.rate_pos u).ne')

/-- At a continuity point of the rate along the inverse, the constructed clock
has exactly the desired derivative. -/
theorem hasDerivAt_clock (t : ℝ) (ht : ContinuousAt r.rate (r.clock t)) :
    HasDerivAt r.clock (r.rate (r.clock t)) t := by
  have h := HasDerivAt.of_local_left_inverse r.clock_continuous.continuousAt
    (r.hasDerivAt_elapsed (r.clock t) ht)
    (inv_ne_zero (r.rate_pos (r.clock t)).ne')
    (Eventually.of_forall r.elapsed_clock)
  simpa only [inv_inv] using h

theorem locallyIntegrable_inv_rate : LocallyIntegrable (fun u => (r.rate u)⁻¹) volume := by
  apply (locallyIntegrable_const r.lower⁻¹).mono r.measurable_rate.inv.aestronglyMeasurable
  apply Eventually.of_forall
  intro u
  simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr r.lower_pos)] using
    r.norm_inv_rate_le u

/-- The elapsed integral has its expected derivative almost everywhere. -/
theorem ae_hasDerivAt_elapsed :
    ∀ᵐ u : ℝ, HasDerivAt r.elapsed (r.rate u)⁻¹ u := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral r.locallyIntegrable_inv_rate] with u hu
  exact hu 0

/-- A Lipschitz elapsed map sends every null exceptional set to a null set.
This transfers almost-everywhere assertions to the inverse clock. -/
theorem ae_comp_clock {P : ℝ → Prop} (hP : ∀ᵐ u : ℝ, P u) :
    ∀ᵐ t : ℝ, P (r.clock t) := by
  have hbad : volume {u : ℝ | ¬ P u} = 0 := by
    exact ae_iff.mp hP
  have himage : volume (r.elapsed '' {u : ℝ | ¬ P u}) = 0 := by
    apply le_antisymm _ bot_le
    have h := r.elapsed_lipschitz.hausdorffMeasure_image_le
      (d := 1) zero_le_one {u : ℝ | ¬ P u}
    simpa only [hausdorffMeasure_real, hbad, mul_zero] using h
  have hnot : ∀ᵐ t : ℝ, t ∉ r.elapsed '' {u : ℝ | ¬ P u} := by
    exact ae_iff.mpr (by simpa only [not_not] using himage)
  filter_upwards [hnot] with t ht
  by_contra h
  exact ht ⟨r.clock t, h, r.elapsed_clock t⟩

/-- The constructed clock satisfies the measurable-rate ODE almost everywhere,
including when the given rate is discontinuous. -/
theorem ae_hasDerivAt_clock :
    ∀ᵐ t : ℝ, HasDerivAt r.clock (r.rate (r.clock t)) t := by
  filter_upwards [r.ae_comp_clock r.ae_hasDerivAt_elapsed] with t ht
  have h := HasDerivAt.of_local_left_inverse r.clock_continuous.continuousAt ht
    (inv_ne_zero (r.rate_pos (r.clock t)).ne')
    (Eventually.of_forall r.elapsed_clock)
  simpa only [inv_inv] using h

theorem clock_absolutelyContinuousOnInterval (a b : ℝ) :
    AbsolutelyContinuousOnInterval r.clock a b :=
  r.clock_lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval

theorem elapsed_absolutelyContinuousOnInterval (a b : ℝ) :
    AbsolutelyContinuousOnInterval r.elapsed a b :=
  r.elapsed_lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval

/-- The inverse maps the nonnegative half-line into itself. -/
theorem clock_mapsTo_nonnegative : MapsTo r.clock (Ici 0) (Ici 0) := by
  intro t ht
  exact (r.clock_nonneg_iff t).mpr ht

/-- The inverse clock restricted to the nonnegative half-line is onto that half-line. -/
theorem clock_surjOn_nonnegative : SurjOn r.clock (Ici 0) (Ici 0) := by
  intro u hu
  refine ⟨r.elapsed u, ?_, r.clock_elapsed u⟩
  exact (r.clock_nonneg_iff (r.elapsed u)).mp (by simpa only [r.clock_elapsed] using hu)

end BoundedPositiveRate

/-- Extend a positive bounded measurable rate given on nonnegative times by `1`
at negative times. Only its values on `[0,∞)` enter the nonnegative elapsed integral. -/
def extendNonnegative (f : ℝ → ℝ) (hf : Measurable f) (m M : ℝ) (hm : 0 < m)
    (hlo : ∀ u, 0 ≤ u → m ≤ f u) (hup : ∀ u, 0 ≤ u → f u ≤ M) :
    BoundedPositiveRate where
  rate := (Ici 0).piecewise f (fun _ => 1)
  measurable_rate := hf.piecewise measurableSet_Ici measurable_const
  lower := min m 1
  upper := max M 1
  lower_pos := lt_min hm zero_lt_one
  lower_bound := by
    intro u
    by_cases hu : 0 ≤ u
    · simpa only [piecewise_eq_of_mem (Ici 0) f (fun _ => 1) hu] using
        (min_le_left m 1).trans (hlo u hu)
    · simpa only [piecewise_eq_of_notMem (Ici 0) f (fun _ => 1) hu] using min_le_right m 1
  upper_bound := by
    intro u
    by_cases hu : 0 ≤ u
    · simpa only [piecewise_eq_of_mem (Ici 0) f (fun _ => 1) hu] using
        (hup u hu).trans (le_max_left M 1)
    · simpa only [piecewise_eq_of_notMem (Ici 0) f (fun _ => 1) hu] using le_max_right M 1

theorem extendNonnegative_rate_of_nonneg (f : ℝ → ℝ) (hf : Measurable f)
    (m M : ℝ) (hm : 0 < m)
    (hlo : ∀ u, 0 ≤ u → m ≤ f u) (hup : ∀ u, 0 ≤ u → f u ≤ M)
    (u : ℝ) (hu : 0 ≤ u) :
    (extendNonnegative f hf m M hm hlo hup).rate u = f u :=
  piecewise_eq_of_mem (Ici 0) f (fun _ => 1) hu

theorem extendNonnegative_rate_of_neg (f : ℝ → ℝ) (hf : Measurable f)
    (m M : ℝ) (hm : 0 < m)
    (hlo : ∀ u, 0 ≤ u → m ≤ f u) (hup : ∀ u, 0 ≤ u → f u ≤ M)
    (u : ℝ) (hu : u < 0) :
    (extendNonnegative f hf m M hm hlo hup).rate u = 1 :=
  piecewise_eq_of_notMem (Ici 0) f (fun _ => 1) (not_le.mpr hu)

end Metastability.PositiveClock
