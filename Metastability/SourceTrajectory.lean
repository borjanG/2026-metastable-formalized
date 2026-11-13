import Metastability.ActualPilot

/-!
# Extending a source solution to the two-particle pilot carrier

The source solution is assumed differentiable only within the nonnegative
half-line. Its continuity there follows from that premise. Constant extension
to negative times supplies the globally continuous carrier used by the inverse
clock construction, without an additional continuity or negative-time ODE
assumption on the source solution.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Metastability.SourceTrajectory

variable {n d : ℕ} {β : ℝ} {model : Source.Model}

/-- Constant extension of the nonnegative-time source solution. -/
def extend (X : ℝ → Source.Configuration n d) (u : ℝ) : Source.Configuration n d :=
  X (max 0 u)

theorem extend_eq_of_nonneg (X : ℝ → Source.Configuration n d) {u : ℝ} (hu : 0 ≤ u) :
    extend X u = X u := by
  simp only [extend, max_eq_right hu]

theorem continuous_coordinate_extend (X : ℝ → Source.Configuration n d)
    (hX : Source.Solves model β X) (i : Fin n) :
    Continuous (fun u => extend X u i) := by
  have hc : ContinuousOn (fun u => (X u i).val) (Ici 0) :=
    fun u hu => (hX u hu i).continuousWithinAt
  apply continuous_induced_rng.mpr
  exact hc.comp_continuous (continuous_const.max continuous_id) (fun u => le_max_left 0 u)

theorem hasDerivAt_coordinate_extend (X : ℝ → Source.Configuration n d)
    (hX : Source.Solves model β X) (i : Fin n) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => (extend X v i).val) (Source.vectorField model β (X u) i) u := by
  have hd := (hX u hu.le i).hasDerivAt (Ici_mem_nhds hu)
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  simp only [extend, max_eq_right hv.le]

theorem configuration_eq_pair (X : Source.Configuration 2 d) :
    TwoParticleSource.configuration (X 0) (X 1) = X := by
  ext i
  fin_cases i <;> rfl

/-- Every source two-particle USA solution produces the pilot trajectory,
using only the source ODE premise. -/
def trajectory (β : ℝ) (X : ℝ → Source.Configuration 2 d)
    (hX : Source.Solves .usa β X) : ActualPilot.Trajectory β d where
  x := fun u => extend X u 0
  y := fun u => extend X u 1
  continuous_x := continuous_coordinate_extend X hX 0
  continuous_y := continuous_coordinate_extend X hX 1
  ode_x := by
    intro u hu
    have hd := hasDerivAt_coordinate_extend X hX 0 hu
    have hf := TwoParticleSource.vectorField_zero β (X u 0) (X u 1)
    rw [configuration_eq_pair (X u)] at hf
    rw [hf] at hd
    simpa only [extend, max_eq_right hu.le] using hd
  ode_y := by
    intro u hu
    have hd := hasDerivAt_coordinate_extend X hX 1 hu
    have hf := TwoParticleSource.vectorField_one β (X u 0) (X u 1)
    rw [configuration_eq_pair (X u)] at hf
    rw [hf] at hd
    simpa only [extend, max_eq_right hu.le] using hd

theorem trajectory_x_of_nonneg (β : ℝ) (X : ℝ → Source.Configuration 2 d)
    (hX : Source.Solves .usa β X) {u : ℝ} (hu : 0 ≤ u) :
    (trajectory β X hX).x u = X u 0 := by
  change extend X u 0 = X u 0
  rw [extend_eq_of_nonneg X hu]

theorem trajectory_y_of_nonneg (β : ℝ) (X : ℝ → Source.Configuration 2 d)
    (hX : Source.Solves .usa β X) {u : ℝ} (hu : 0 ≤ u) :
    (trajectory β X hX).y u = X u 1 := by
  change extend X u 1 = X u 1
  rw [extend_eq_of_nonneg X hu]

theorem trajectory_configuration_of_nonneg (β : ℝ) (X : ℝ → Source.Configuration 2 d)
    (hX : Source.Solves .usa β X) {u : ℝ} (hu : 0 ≤ u) :
    (trajectory β X hX).configuration u = X u := by
  rw [ActualPilot.Trajectory.configuration,
    trajectory_x_of_nonneg β X hX hu, trajectory_y_of_nonneg β X hX hu]
  exact configuration_eq_pair (X u)

/-- At nonnegative accelerated times the pilot energy is the literal energy of
the original source solution under the constructed clock. -/
theorem trajectory_energy_eq_source (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Source.Configuration 2 d) (hX : Source.Solves .usa β X)
    {t : ℝ} (ht : 0 ≤ t) :
    (trajectory β X hX).energy hβ t =
      Source.energy β (X ((trajectory β X hX).clock hβ t)) := by
  unfold ActualPilot.Trajectory.energy
  have hnonneg : 0 ≤ (trajectory β X hX).clock hβ t :=
    ((trajectory β X hX).boundedRate hβ).clock_nonneg_iff t |>.mpr ht
  exact congrArg (Source.energy β) (trajectory_configuration_of_nonneg β X hX hnonneg)

/-- The clock built from the constant extension satisfies the literal source
clock relation for the unextended solution on nonnegative times. -/
theorem trajectory_clockRelation_source (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Source.Configuration 2 d) (hX : Source.Solves .usa β X) :
    Source.ClockRelation β X 0 ((trajectory β X hX).clock hβ) := by
  let p := trajectory β X hX
  have hcfg : ∀ u, 0 ≤ u → p.configuration u = X u :=
    fun u hu => trajectory_configuration_of_nonneg β X hX hu
  have hint : ∀ u, 0 ≤ u →
      Source.originalClockTime β p.configuration 0 u = Source.originalClockTime β X 0 u := by
    intro u hu
    unfold Source.originalClockTime
    apply intervalIntegral.integral_congr
    intro v hv
    have hv0 : 0 ≤ v := by
      rw [uIcc_of_le hu] at hv
      exact hv.1
    simp only [zero_add, hcfg v hv0]
  obtain ⟨⟨hzero, hnonneg, hac, hderiv⟩, hstrict, hintnonneg, hleft, hright⟩ :=
    p.clockRelation hβ
  refine ⟨⟨hzero, hnonneg, hac, ?_⟩, hstrict, ?_, ?_, ?_⟩
  · filter_upwards [hderiv, MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht htm
    simpa only [Source.accelerated, zero_add, hcfg _ (hnonneg t htm)] using ht
  · intro u hu
    rw [← hint u hu]
    exact hintnonneg u hu
  · intro t ht
    rw [← hint _ (hnonneg t ht)]
    exact hleft t ht
  · intro u hu
    rw [← hint u hu]
    exact hright u hu

end Metastability.SourceTrajectory
