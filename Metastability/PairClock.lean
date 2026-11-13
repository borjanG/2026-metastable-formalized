import Metastability.SourceDefinitions
import Metastability.PositiveClock
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Constructing the two-particle cutoff clock

The rate uses the manuscript's angular cutoff, including the fallback value one.
For continuous sphere-valued trajectories it is a bounded positive measurable
rate, so the inverse-integral construction applies. The trajectories in this
module are defined on the real line; a source trajectory on the half-line can
be extended constantly to negative times.
-/

noncomputable section
open scoped RealInnerProductSpace Topology
open Set

namespace Metastability.PairClock

variable {d : ℕ}

/-- The exact two-particle cutoff rate. -/
def rate (β : ℝ) (x y : Source.Sphere d) : ℝ :=
  if Source.clockCutoff β < Source.angularDist x y then
    Real.log β * Real.exp (β * (1 - ⟪x.val, y.val⟫))
  else 1

theorem correlation_bounds (x y : Source.Sphere d) :
    -1 ≤ ⟪x.val, y.val⟫ ∧ ⟪x.val, y.val⟫ ≤ 1 := by
  have h : |⟪x.val, y.val⟫| ≤ 1 := by
    simpa only [x.property, y.property, mul_one] using abs_real_inner_le_norm x.val y.val
  exact abs_le.mp h

theorem rate_bounds (β : ℝ) (hβ : 1 < β) (x y : Source.Sphere d) :
    min 1 (Real.log β) ≤ rate β x y ∧
      rate β x y ≤ max 1 (Real.log β * Real.exp (2 * β)) := by
  have hl : 0 < Real.log β := Real.log_pos hβ
  have hb : 0 ≤ β := by linarith
  obtain ⟨hrl, hru⟩ := correlation_bounds x y
  unfold rate
  split_ifs with h
  · have he0 : 1 ≤ Real.exp (β * (1 - ⟪x.val, y.val⟫)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hb (sub_nonneg.mpr hru))
    have he1 : Real.exp (β * (1 - ⟪x.val, y.val⟫)) ≤ Real.exp (2 * β) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    constructor
    · exact (min_le_right _ _).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he0 hl.le)
    · exact (mul_le_mul_of_nonneg_left he1 hl.le).trans (le_max_right _ _)
  · exact ⟨min_le_left _ _, le_max_left _ _⟩

theorem measurable_rate (β : ℝ) (x y : ℝ → Source.Sphere d)
    (hx : Continuous x) (hy : Continuous y) :
    Measurable (fun u => rate β (x u) (y u)) := by
  have hxv : Continuous (fun u => (x u).val) := continuous_subtype_val.comp hx
  have hyv : Continuous (fun u => (y u).val) := continuous_subtype_val.comp hy
  have hi : Continuous (fun u => ⟪(x u).val, (y u).val⟫) := hxv.inner hyv
  have ha : Continuous (fun u => Source.angularDist (x u) (y u)) :=
    Real.continuous_arccos.comp hi
  exact Measurable.ite (measurableSet_lt measurable_const ha.measurable)
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub hi)))).measurable
    measurable_const

/-- The actual rate packaged with proved bounds and measurability. -/
def boundedRate (β : ℝ) (hβ : 1 < β) (x y : ℝ → Source.Sphere d)
    (hx : Continuous x) (hy : Continuous y) : PositiveClock.BoundedPositiveRate where
  rate := fun u => rate β (x u) (y u)
  measurable_rate := measurable_rate β x y hx hy
  lower := min 1 (Real.log β)
  upper := max 1 (Real.log β * Real.exp (2 * β))
  lower_pos := lt_min (by norm_num) (Real.log_pos hβ)
  lower_bound := fun u => (rate_bounds β hβ (x u) (y u)).1
  upper_bound := fun u => (rate_bounds β hβ (x u) (y u)).2

/-- The rate is continuous at any original time strictly before the cutoff. -/
theorem continuousAt_rate_of_active (β : ℝ) (x y : ℝ → Source.Sphere d)
    (hx : Continuous x) (hy : Continuous y) {u : ℝ}
    (hu : Source.clockCutoff β < Source.angularDist (x u) (y u)) :
    ContinuousAt (fun v => rate β (x v) (y v)) u := by
  have hi : Continuous (fun v => ⟪(x v).val, (y v).val⟫) :=
    (continuous_subtype_val.comp hx).inner (continuous_subtype_val.comp hy)
  have ha : Continuous (fun v => Source.angularDist (x v) (y v)) :=
    Real.continuous_arccos.comp hi
  have he : ∀ᶠ v in 𝓝 u,
      Source.clockCutoff β < Source.angularDist (x v) (y v) :=
    ha.continuousAt.eventually (lt_mem_nhds hu)
  apply ContinuousAt.congr_of_eventuallyEq
    (f := fun v => Real.log β * Real.exp (β * (1 - ⟪(x v).val, (y v).val⟫)))
  · exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub hi)))).continuousAt
  · filter_upwards [he] with v hv
    simp only [rate, if_pos hv]

/-- The constructed inverse-integral clock has the active Arrhenius rate
wherever the current pair lies strictly above the actual cutoff. -/
theorem hasDerivAt_clock_of_active (β : ℝ) (hβ : 1 < β)
    (x y : ℝ → Source.Sphere d) (hx : Continuous x) (hy : Continuous y) (t : ℝ)
    (ht : Source.clockCutoff β < Source.angularDist
      (x ((boundedRate β hβ x y hx hy).clock t))
      (y ((boundedRate β hβ x y hx hy).clock t))) :
    HasDerivAt (boundedRate β hβ x y hx hy).clock
      (Real.log β * Real.exp (β * (1 - ⟪
        (x ((boundedRate β hβ x y hx hy).clock t)).val,
        (y ((boundedRate β hβ x y hx hy).clock t)).val⟫))) t := by
  have h := (boundedRate β hβ x y hx hy).hasDerivAt_clock t
    (continuousAt_rate_of_active β x y hx hy ht)
  change HasDerivAt (boundedRate β hβ x y hx hy).clock
    (rate β (x ((boundedRate β hβ x y hx hy).clock t))
      (y ((boundedRate β hβ x y hx hy).clock t))) t at h
  rw [rate, if_pos ht] at h
  exact h

end Metastability.PairClock
