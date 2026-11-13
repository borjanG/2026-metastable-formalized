import Metastability.SourceTrajectory

/-!
# The source clock for arbitrary finite configurations

For either source model, the ODE gives continuity on nonnegative times.
The literal angular-cutoff rate is measurable and uniformly positive and bounded.
Its reciprocal integral therefore has a unique inverse on the nonnegative
half-line, with the source's absolute-continuity and almost-everywhere ODE laws.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped RealInnerProductSpace Topology

namespace Metastability.GeneralClock

variable {n d : ℕ}

theorem pair_exponential_bounds (β : ℝ) (hβ : 0 ≤ β) (x y : Source.Sphere d) :
    1 ≤ Real.exp (β * (1 - ⟪x.val, y.val⟫)) ∧
      Real.exp (β * (1 - ⟪x.val, y.val⟫)) ≤ Real.exp (2 * β) := by
  obtain ⟨hl, hu⟩ := PairClock.correlation_bounds x y
  constructor
  · exact Real.one_le_exp_iff.mpr (mul_nonneg hβ (sub_nonneg.mpr hu))
  · apply Real.exp_le_exp.mpr
    nlinarith

/-- Bounds on the literal finite minimum, including its fallback value one. -/
theorem clockFactor_bounds (β : ℝ) (hβ : 1 < β) (x : Source.Configuration n d) :
    min 1 (Real.log β) ≤ Source.clockFactor β x ∧
      Source.clockFactor β x ≤ max 1 (Real.log β * Real.exp (2 * β)) := by
  have hl : 0 < Real.log β := Real.log_pos hβ
  unfold Source.clockFactor
  split_ifs with h
  · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp
      (Finset.min'_mem ((Source.eligiblePairs β x).image fun p =>
        Real.exp (β * (1 - ⟪(x p.1).val, (x p.2).val⟫)))
        (Finset.Nonempty.image h _))
    rw [← hp]
    obtain ⟨helo, hehi⟩ := pair_exponential_bounds β (by linarith) (x p.1) (x p.2)
    constructor
    · exact (min_le_right _ _).trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left helo hl.le)
    · exact (mul_le_mul_of_nonneg_left hehi hl.le).trans (le_max_right _ _)
  · exact ⟨min_le_left _ _, le_max_left _ _⟩

/-- A strict sublevel set of the changing finite minimum is a finite union
of eligible-pair sublevel sets, together with the all-complete fallback. -/
theorem clockFactor_lt_iff (β : ℝ) (hβ : 1 < β) (x : Source.Configuration n d)
    (a : ℝ) :
    Source.clockFactor β x < a ↔
      (¬ (Source.eligiblePairs β x).Nonempty ∧ 1 < a) ∨
      ∃ p ∈ Source.eligiblePairs β x,
        Real.log β * Real.exp (β * (1 - ⟪(x p.1).val, (x p.2).val⟫)) < a := by
  have hl : 0 < Real.log β := Real.log_pos hβ
  unfold Source.clockFactor
  split_ifs with h
  · constructor
    · intro ha
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp
        (Finset.min'_mem ((Source.eligiblePairs β x).image fun p =>
          Real.exp (β * (1 - ⟪(x p.1).val, (x p.2).val⟫)))
          (Finset.Nonempty.image h _))
      exact Or.inr ⟨p, hp, by simpa only [heq] using ha⟩
    · rintro (⟨hn, _⟩ | ⟨p, hp, ha⟩)
      · exact (hn h).elim
      · exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left
            (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)) hl.le) ha
  · constructor
    · exact fun ha => Or.inl ⟨h, ha⟩
    · rintro (⟨_, ha⟩ | ⟨p, hp, _⟩)
      · exact ha
      · exact (h ⟨p, hp⟩).elim

/-- Measurability holds across every eligibility change; no generic-position
or no-tie hypothesis is needed. -/
theorem measurable_clockFactor {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (β : ℝ) (hβ : 1 < β)
    (X : α → Source.Configuration n d) (hX : ∀ i, Continuous (fun u => X u i)) :
    Measurable (fun u => Source.clockFactor β (X u)) := by
  have hi (p : Fin n × Fin n) :
      Continuous (fun u => ⟪(X u p.1).val, (X u p.2).val⟫) :=
    (continuous_subtype_val.comp (hX p.1)).inner
      (continuous_subtype_val.comp (hX p.2))
  have hm (p : Fin n × Fin n) :
      Measurable (fun u => p ∈ Source.eligiblePairs β (X u)) := by
    simp only [Source.eligiblePairs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurable_const.and
      (measurableSet_setOf.mp (measurableSet_lt measurable_const
        (Real.continuous_arccos.comp (hi p)).measurable))
  have hn : Measurable (fun u => (Source.eligiblePairs β (X u)).Nonempty) :=
    Measurable.exists hm
  apply measurable_of_Iio
  intro a
  change MeasurableSet {u | Source.clockFactor β (X u) < a}
  simp_rw [clockFactor_lt_iff β hβ]
  apply Measurable.setOf
  apply (hn.not.and measurable_const).or
  apply Measurable.exists
  intro p
  apply (hm p).and
  apply measurableSet_setOf.mp
  exact measurableSet_lt
    (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.sub (hi p))))).measurable measurable_const

/-- The source configuration rate is Borel measurable. -/
theorem measurable_source_clockFactor (β : ℝ) (hβ : 1 < β) :
    Measurable (Source.clockFactor (n := n) (d := d) β) :=
  measurable_clockFactor β hβ id continuous_apply

/-- The shifted source trajectory, extended constantly before original time zero. -/
def shiftedConfiguration (X : ℝ → Source.Configuration n d) (shift u : ℝ) :
    Source.Configuration n d := SourceTrajectory.extend X (shift + u)

theorem shiftedConfiguration_eq (X : ℝ → Source.Configuration n d)
    {shift u : ℝ} (hshift : 0 ≤ shift) (hu : 0 ≤ u) :
    shiftedConfiguration X shift u = X (shift + u) :=
  SourceTrajectory.extend_eq_of_nonneg X (add_nonneg hshift hu)

theorem continuous_shifted_coordinate {model : Source.Model} {β : ℝ}
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (shift : ℝ) (i : Fin n) :
    Continuous (fun u => shiftedConfiguration X shift u i) :=
  (SourceTrajectory.continuous_coordinate_extend X hX i).comp
    (continuous_const.add continuous_id)

/-- The exact source rate along the shifted, extended solution, with all
measurability and bound obligations proved from the source ODE. -/
def boundedRate {model : Source.Model} (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (shift : ℝ) : PositiveClock.BoundedPositiveRate where
  rate := fun u => Source.clockFactor β (shiftedConfiguration X shift u)
  measurable_rate := measurable_clockFactor β hβ (shiftedConfiguration X shift)
    (continuous_shifted_coordinate X hX shift)
  lower := min 1 (Real.log β)
  upper := max 1 (Real.log β * Real.exp (2 * β))
  lower_pos := lt_min zero_lt_one (Real.log_pos hβ)
  lower_bound := fun _ => (clockFactor_bounds β hβ _).1
  upper_bound := fun _ => (clockFactor_bounds β hβ _).2

theorem boundedRate_rate_of_nonneg {model : Source.Model} (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    {shift u : ℝ} (hshift : 0 ≤ shift) (hu : 0 ≤ u) :
    (boundedRate β hβ X hX shift).rate u = Source.clockFactor β (X (shift + u)) := by
  change Source.clockFactor β (shiftedConfiguration X shift u) = _
  rw [shiftedConfiguration_eq X hshift hu]

theorem elapsed_eq_originalClockTime {model : Source.Model} (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    {shift u : ℝ} (hshift : 0 ≤ shift) (hu : 0 ≤ u) :
    (boundedRate β hβ X hX shift).elapsed u = Source.originalClockTime β X shift u := by
  unfold PositiveClock.BoundedPositiveRate.elapsed Source.originalClockTime
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hu] at hv
  exact congrArg (fun a : ℝ => a⁻¹)
    (boundedRate_rate_of_nonneg β hβ X hX hshift hv.1)

/-- The constructed clock satisfies every source condition for arbitrary
finite particle count and either source model, without a clock premise. -/
theorem clockRelation {model : Source.Model} (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) :
    Source.ClockRelation β X shift (boundedRate β hβ X hX shift).clock := by
  let r := boundedRate β hβ X hX shift
  have hrate : ∀ u, 0 ≤ u → r.rate u = Source.clockFactor β (X (shift + u)) :=
    fun u hu => boundedRate_rate_of_nonneg β hβ X hX hshift hu
  have hint : ∀ u, 0 ≤ u → r.elapsed u = Source.originalClockTime β X shift u :=
    fun u hu => elapsed_eq_originalClockTime β hβ X hX hshift hu
  refine ⟨?_, r.clock_strictMono.strictMonoOn _, ?_, ?_, ?_⟩
  · refine ⟨r.clock_zero, ?_, ?_, ?_⟩
    · intro t ht
      exact r.clock_mapsTo_nonnegative ht
    · intro b _
      exact r.clock_absolutelyContinuousOnInterval 0 b
    · have ha := ae_restrict_of_ae (s := Ici (0 : ℝ)) r.ae_hasDerivAt_clock
      filter_upwards [ha, ae_restrict_mem measurableSet_Ici] with t ht htm
      rw [hrate _ (r.clock_mapsTo_nonnegative htm)] at ht
      exact ht
  · intro u hu
    rw [← hint u hu]
    have h := r.elapsed_strictMono.monotone hu
    simpa only [PositiveClock.BoundedPositiveRate.elapsed_zero] using h
  · intro t ht
    rw [← hint _ (r.clock_mapsTo_nonnegative ht)]
    exact r.elapsed_clock t
  · intro u hu
    rw [← hint u hu]
    exact r.clock_elapsed u

/-- Existence of the source clock from the source ODE alone, for both models. -/
theorem exists_clockRelation {model : Source.Model} (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) :
    ∃ clock : ℝ → ℝ, Source.ClockRelation β X shift clock :=
  ⟨(boundedRate β hβ X hX shift).clock, clockRelation β hβ X hX shift hshift⟩

/-- The source integral identities determine the clock uniquely on its
nonnegative-time domain. They impose no uniqueness condition at negative times. -/
theorem clockRelation_unique_on_nonnegative {β shift : ℝ}
    {X : ℝ → Source.Configuration n d} {clock₁ clock₂ : ℝ → ℝ}
    (h₁ : Source.ClockRelation β X shift clock₁)
    (h₂ : Source.ClockRelation β X shift clock₂) : EqOn clock₁ clock₂ (Ici 0) := by
  obtain ⟨_, _, _, _, h₁right⟩ := h₁
  obtain ⟨⟨_, h₂nonneg, _, _⟩, _, _, h₂left, _⟩ := h₂
  intro t ht
  calc
    clock₁ t = clock₁ (Source.originalClockTime β X shift (clock₂ t)) :=
      congrArg clock₁ (h₂left t ht).symm
    _ = clock₂ t := h₁right _ (h₂nonneg t ht)

end Metastability.GeneralClock
