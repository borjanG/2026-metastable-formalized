import Metastability.TwoParticleSource
import Metastability.ScalarHitting
import Metastability.PilotGeometry
import Metastability.PilotHalfline

/-!
# Actual two-particle USA trajectories and their cutoff clock

A trajectory contains the two vector ODEs, continuity, and unit norms only.
No scalar equation, hitting-time estimate, or asymptotic conclusion is assumed.
The harmless negative-time part is used to construct a global inverse; dynamics
are required only at positive original times.
-/

noncomputable section
open scoped RealInnerProductSpace Topology
open Set Filter

namespace Metastability.ActualPilot

structure Trajectory (β : ℝ) (d : ℕ) where
  x : ℝ → Source.Sphere d
  y : ℝ → Source.Sphere d
  continuous_x : Continuous x
  continuous_y : Continuous y
  ode_x : ∀ u, 0 < u → HasDerivAt (fun v => (x v).val)
    (TwoParticle.twoParticleVelocityWithSelf β (x u).val (y u).val) u
  ode_y : ∀ u, 0 < u → HasDerivAt (fun v => (y v).val)
    (TwoParticle.twoParticleVelocityWithSelf β (y u).val (x u).val) u

namespace Trajectory
variable {β : ℝ} {d : ℕ} (p : Trajectory β d)

def correlation (u : ℝ) : ℝ := ⟪(p.x u).val, (p.y u).val⟫
def configuration (u : ℝ) : Source.Configuration 2 d :=
  TwoParticleSource.configuration (p.x u) (p.y u)
def boundedRate (hβ : 1 < β) : PositiveClock.BoundedPositiveRate :=
  PairClock.boundedRate β hβ p.x p.y p.continuous_x p.continuous_y

def clock (hβ : 1 < β) : ℝ → ℝ := (p.boundedRate hβ).clock
def energy (hβ : 1 < β) (t : ℝ) : ℝ :=
  Source.energy β (p.configuration (p.clock hβ t))

theorem continuous_correlation : Continuous p.correlation :=
  (continuous_subtype_val.comp p.continuous_x).inner
    (continuous_subtype_val.comp p.continuous_y)

theorem correlation_bounds (u : ℝ) : p.correlation u ∈ Icc (-1 : ℝ) 1 :=
  PairClock.correlation_bounds (p.x u) (p.y u)

theorem scalarODE (u : ℝ) (hu : 0 < u) :
    HasDerivAt p.correlation
      ((1 - p.correlation u ^ 2) * Real.exp (β * (p.correlation u - 1))) u :=
  TwoParticle.hasDerivAt_inner_of_fullUSA β (fun v => (p.x v).val)
    (fun v => (p.y v).val) u (p.x u).property (p.y u).property
    (p.ode_x u hu) (p.ode_y u hu)

theorem monotone_correlation : MonotoneOn p.correlation (Ici 0) :=
  ScalarHitting.monotoneOn_of_scalarODE β p.correlation
    p.continuous_correlation.continuousOn p.scalarODE (fun u _ => p.correlation_bounds u)

theorem energy_eq_scalar (hβ : 1 < β) (t : ℝ) :
    p.energy hβ t = (1 + Real.exp (β * (p.correlation (p.clock hβ t) - 1))) / 2 := by
  rw [energy, configuration, TwoParticleSource.energy_eq, TwoParticle.twoParticleEnergy_eq]
  · rfl
  · exact (p.x _).property
  · exact (p.y _).property

theorem energy_le_one (hβ : 1 < β) (t : ℝ) : p.energy hβ t ≤ 1 := by
  rw [p.energy_eq_scalar hβ t]
  have he : Real.exp (β * (p.correlation (p.clock hβ t) - 1)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [(p.correlation_bounds (p.clock hβ t)).2])
  linarith

theorem monotone_energy (hβ : 1 < β) : MonotoneOn (p.energy hβ) (Ici 0) := by
  intro s hs t ht hst
  rw [p.energy_eq_scalar hβ s, p.energy_eq_scalar hβ t]
  have hm : p.correlation (p.clock hβ s) ≤ p.correlation (p.clock hβ t) :=
    p.monotone_correlation ((p.boundedRate hβ).clock_nonneg_iff s |>.mpr hs)
      ((p.boundedRate hβ).clock_nonneg_iff t |>.mpr ht)
      ((p.boundedRate hβ).clock_strictMono.monotone hst)
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right hm 1)
    (by linarith : 0 ≤ β))
  linarith

/-- The constructed clock satisfies the source's integral, differential, and
absolute-continuity conditions for the literal two-label configuration. -/
theorem clockRelation (hβ : 1 < β) :
    Source.ClockRelation β p.configuration 0 (p.clock hβ) := by
  have hrate : ∀ u, Source.clockFactor β (p.configuration u) = (p.boundedRate hβ).rate u := by
    intro u
    exact TwoParticleSource.clockFactor_eq β (p.x u) (p.y u)
  have helapsed : ∀ u, Source.originalClockTime β p.configuration 0 u =
      (p.boundedRate hβ).elapsed u := by
    intro u
    simp only [Source.originalClockTime, zero_add, hrate, PositiveClock.BoundedPositiveRate.elapsed]
  refine ⟨?_, (p.boundedRate hβ).clock_strictMono.strictMonoOn _, ?_, ?_, ?_⟩
  · refine ⟨(p.boundedRate hβ).clock_zero, ?_, ?_, ?_⟩
    · intro t ht
      exact (p.boundedRate hβ).clock_mapsTo_nonnegative ht
    · intro b _
      exact (p.boundedRate hβ).clock_absolutelyContinuousOnInterval 0 b
    · have ha := MeasureTheory.ae_restrict_of_ae (s := Ici (0 : ℝ))
        (p.boundedRate hβ).ae_hasDerivAt_clock
      filter_upwards [ha] with t ht
      simpa only [Source.accelerated, zero_add, hrate, clock] using ht
  · intro u hu
    rw [helapsed]
    have h := (p.boundedRate hβ).elapsed_strictMono.monotone hu
    simpa only [PositiveClock.BoundedPositiveRate.elapsed_zero] using h
  · intro t _
    rw [helapsed]
    exact (p.boundedRate hβ).elapsed_clock t
  · intro u _
    rw [helapsed]
    exact (p.boundedRate hβ).clock_elapsed u

/-- The actual cutoff clock follows the analytic profile through its first
cutoff crossing. In particular, the algebraic cutoff time is the dynamical
hitting time; no hitting-time or scalar-flow hypothesis is supplied. -/
theorem profile_until_cutoff (hβ : 1 < β) {a : ℝ} (ha : 0 < a)
    (hstart : -1 < p.correlation 0)
    (hodds : ScalarClock.odds (p.correlation 0) = a ^ 2)
    (hbelow : p.correlation 0 < Real.cos (Source.clockCutoff β))
    (hsmall : Source.clockCutoff β < Real.pi) :
    0 < PilotCutoff.cutoffTime a β ∧
      (p.correlation (p.clock hβ (PilotCutoff.cutoffTime a β)) =
        Real.cos (Source.clockCutoff β)) ∧
      ∀ t ∈ Icc 0 (PilotCutoff.cutoffTime a β),
        p.energy hβ t = PilotAsymptotics.analyticEnergy a β t := by
  have hcutpos : 0 < Source.clockCutoff β := by
    rw [PilotGeometry.clockCutoff_eq_angularCutoff]
    exact PilotCutoff.angularCutoff_pos hβ
  have htarget : Real.cos (Source.clockCutoff β) < 1 := by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hsmall.le hcutpos
  obtain ⟨U, hU, hhit, hbefore, _⟩ := ScalarHitting.exists_first_hit β
    (Real.cos (Source.clockCutoff β)) p.correlation (by linarith)
    p.continuous_correlation.continuousOn p.scalarODE (fun u _ => p.correlation_bounds u)
    hstart hbelow htarget
  let V := (p.boundedRate hβ).elapsed U
  have hV : 0 < V := by
    simpa only [PositiveClock.BoundedPositiveRate.elapsed_zero] using
      (p.boundedRate hβ).elapsed_strictMono hU
  have hclockV : p.clock hβ V = U := (p.boundedRate hβ).clock_elapsed U
  have hactive : ∀ t ∈ Ioo 0 V, HasDerivAt (p.clock hβ)
      (Real.log β * Real.exp (β * (1 - p.correlation (p.clock hβ t)))) t := by
    intro t ht
    apply PairClock.hasDerivAt_clock_of_active β hβ p.x p.y p.continuous_x p.continuous_y
    apply (PilotGeometry.cutoff_lt_angularDist_iff β _ _ hcutpos.le hsmall.le).mpr
    have hct : p.clock hβ t < U := by
      rw [← hclockV]
      exact (p.boundedRate hβ).clock_strictMono ht.2
    exact hbefore _ ((p.boundedRate hβ).clock_nonneg_iff t |>.mpr ht.1.le) hct
  have hprofile : ∀ t ∈ Icc 0 V, p.correlation (p.clock hβ t) =
      PilotAsymptotics.cosineProfile a β t := by
    intro t ht
    exact PilotHalfline.correlation_eq_profile β a V hβ
      (fun u => (p.x u).val) (fun u => (p.y u).val) (p.clock hβ)
      (continuous_subtype_val.comp p.continuous_x).continuousOn
      (continuous_subtype_val.comp p.continuous_y).continuousOn
      (p.boundedRate hβ).clock_continuous.continuousOn
      (p.boundedRate hβ).clock_zero ((p.boundedRate hβ).clock_strictMono.strictMonoOn _)
      (fun u _ => (p.x u).property) (fun u _ => (p.y u).property)
      p.ode_x p.ode_y hactive hstart hodds ht
  have hVeq : V = PilotCutoff.cutoffTime a β :=
    (PilotGeometry.cosineProfile_eq_cos_clockCutoff_iff ha hβ hsmall).mp (by
      rw [← hprofile V ⟨hV.le, le_rfl⟩, hclockV]
      exact hhit)
  refine ⟨hVeq ▸ hV, ?_, ?_⟩
  · rw [← hVeq, hclockV]
    exact hhit
  · intro t ht
    rw [p.energy_eq_scalar hβ t, hprofile t (hVeq ▸ ht)]
    exact (PilotAsymptotics.analyticEnergy_eq_cosine a β t).symm

end Trajectory
end Metastability.ActualPilot
