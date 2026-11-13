import Metastability.PositiveClock
import Metastability.ScalarHitting
import Metastability.TwoParticle

/-!
# Transporting the first cutoff through the constructed clock

These scalar assembly lemmas are used after deriving the scalar ODE from the
particle system. The active-rate equality is used only on the original-time
open interval before the proved first hit; it is not an assumed scalar law.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Metastability.StoppedEnergy

open PositiveClock

theorem clock_lt_elapsed_iff (R : BoundedPositiveRate) (t u : ℝ) :
    R.clock t < u ↔ t < R.elapsed u := by
  simpa only [R.elapsed_clock] using
    (R.elapsed_strictMono.lt_iff_lt (a := R.clock t) (b := u)).symm

theorem clock_le_elapsed_iff (R : BoundedPositiveRate) (t u : ℝ) :
    R.clock t ≤ u ↔ t ≤ R.elapsed u := by
  simpa only [R.elapsed_clock] using
    (R.elapsed_strictMono.le_iff_le (a := R.clock t) (b := u)).symm

theorem elapsed_le_clock_iff (R : BoundedPositiveRate) (u t : ℝ) :
    u ≤ R.clock t ↔ R.elapsed u ≤ t := by
  simpa only [R.elapsed_clock] using
    (R.elapsed_strictMono.le_iff_le (a := u) (b := R.clock t)).symm

theorem clock_pos_iff (R : BoundedPositiveRate) (t : ℝ) :
    0 < R.clock t ↔ 0 < t := by
  simpa only [R.clock_zero] using (R.clock_strictMono.lt_iff_lt (a := 0) (b := t))

theorem elapsed_pos (R : BoundedPositiveRate) {U : ℝ} (hU : 0 < U) :
    0 < R.elapsed U := by
  simpa only [R.elapsed_zero] using R.elapsed_strictMono hU

theorem clock_mapsTo_closed_stage (R : BoundedPositiveRate) (U : ℝ) :
    MapsTo R.clock (Icc 0 (R.elapsed U)) (Icc 0 U) := by
  intro t ht
  exact ⟨(R.clock_nonneg_iff t).mpr ht.1, (clock_le_elapsed_iff R t U).mpr ht.2⟩

theorem clock_mapsTo_open_stage (R : BoundedPositiveRate) (U : ℝ) :
    MapsTo R.clock (Ioo 0 (R.elapsed U)) (Ioo 0 U) := by
  intro t ht
  exact ⟨(clock_pos_iff R t).mpr ht.1, (clock_lt_elapsed_iff R t U).mpr ht.2⟩

/-- A first original-time hit transfers to the actual constructed clock. -/
theorem first_hit_transport (R : BoundedPositiveRate) (ρ : ℝ → ℝ) (q U : ℝ)
    (hU : 0 < U) (hhit : ρ U = q)
    (hbefore : ∀ u : ℝ, 0 ≤ u → u < U → ρ u < q)
    (hafter : ∀ u : ℝ, U ≤ u → q ≤ ρ u) :
    0 < R.elapsed U ∧ ρ (R.clock (R.elapsed U)) = q ∧
      (∀ t : ℝ, 0 ≤ t → t < R.elapsed U → ρ (R.clock t) < q) ∧
      (∀ t : ℝ, R.elapsed U ≤ t → q ≤ ρ (R.clock t)) := by
  refine ⟨elapsed_pos R hU, ?_, ?_, ?_⟩
  · simpa only [R.clock_elapsed] using hhit
  · intro t ht htU
    exact hbefore (R.clock t) ((R.clock_nonneg_iff t).mpr ht)
      ((clock_lt_elapsed_iff R t U).mpr htU)
  · intro t ht
    exact hafter (R.clock t) ((elapsed_le_clock_iff R U t).mpr ht)

/-- Existence and the first-hit properties in both time variables follow from
the original scalar ODE and the independently constructed inverse clock. -/
theorem exists_accelerated_first_hit (R : BoundedPositiveRate) (β q : ℝ) (ρ : ℝ → ℝ)
    (hβ : 0 < β) (hc : ContinuousOn ρ (Ici 0))
    (hd : ∀ u, 0 < u →
      HasDerivAt ρ ((1 - (ρ u) ^ 2) * Real.exp (β * (ρ u - 1))) u)
    (hb : ∀ u, 0 ≤ u → ρ u ∈ Icc (-1 : ℝ) 1)
    (hρ₀ : -1 < ρ 0) (hinitial : ρ 0 < q) (hq : q < 1) :
    ∃ U : ℝ, 0 < U ∧ ρ U = q ∧ 0 < R.elapsed U ∧
      (∀ t : ℝ, 0 ≤ t → t < R.elapsed U → ρ (R.clock t) < q) ∧
      (∀ t : ℝ, R.elapsed U ≤ t → q ≤ ρ (R.clock t)) := by
  obtain ⟨U, hU, hhit, hbefore, hafter⟩ :=
    ScalarHitting.exists_first_hit β q ρ hβ hc hd hb hρ₀ hinitial hq
  obtain ⟨hV, _, hbefore', hafter'⟩ := first_hit_transport R ρ q U hU hhit hbefore hafter
  exact ⟨U, hU, hhit, hV, hbefore', hafter'⟩

/-- On the open active interval the rate is continuous, even though it may jump
at the cutoff. The hypotheses require only continuity of the original scalar path. -/
theorem continuousAt_rate_before (R : BoundedPositiveRate) (β U : ℝ) (ρ : ℝ → ℝ)
    (hc : ContinuousOn ρ (Ici 0))
    (hactive : ∀ u ∈ Ioo 0 U,
      R.rate u = Real.log β * Real.exp (β * (1 - ρ u)))
    {u : ℝ} (hu : u ∈ Ioo 0 U) : ContinuousAt R.rate u := by
  have hρu : ContinuousAt ρ u := hc.continuousAt (Ici_mem_nhds hu.1)
  apply ContinuousAt.congr_of_eventuallyEq
    (f := fun v => Real.log β * Real.exp (β * (1 - ρ v)))
  · exact continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (continuousAt_const.sub hρu)))
  · filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
    exact hactive v hv

/-- The accelerated scalar law is derived on the entire open pre-cutoff stage
from the original scalar ODE and the rate of the constructed inverse clock. -/
theorem hasDerivAt_accelerated_before (R : BoundedPositiveRate) (β U : ℝ) (ρ : ℝ → ℝ)
    (hc : ContinuousOn ρ (Ici 0))
    (hd : ∀ u, 0 < u →
      HasDerivAt ρ ((1 - (ρ u) ^ 2) * Real.exp (β * (ρ u - 1))) u)
    (hactive : ∀ u ∈ Ioo 0 U,
      R.rate u = Real.log β * Real.exp (β * (1 - ρ u)))
    {t : ℝ} (ht : t ∈ Ioo 0 (R.elapsed U)) :
    HasDerivAt (fun s => ρ (R.clock s))
      ((1 - (ρ (R.clock t)) ^ 2) * Real.log β) t := by
  have hu := clock_mapsTo_open_stage R U ht
  have hclock := R.hasDerivAt_clock t (continuousAt_rate_before R β U ρ hc hactive hu)
  rw [hactive (R.clock t) hu] at hclock
  have h := (hd (R.clock t) hu.1).comp t hclock
  rw [TwoParticle.scalar_clock_cancellation] at h
  exact h

theorem continuousOn_accelerated_closed_stage (R : BoundedPositiveRate) (U : ℝ)
    (ρ : ℝ → ℝ) (hc : ContinuousOn ρ (Ici 0)) :
    ContinuousOn (fun t => ρ (R.clock t)) (Icc 0 (R.elapsed U)) := by
  exact hc.comp R.clock_continuous.continuousOn
    (fun t ht => (R.clock_nonneg_iff t).mpr ht.1)

/-- Once the rate has switched permanently to one, the constructed clock is
exactly original time plus a constant. -/
theorem clock_eq_after_switch (R : BoundedPositiveRate) (U : ℝ)
    (hafter : ∀ u : ℝ, U ≤ u → R.rate u = 1)
    {t : ℝ} (ht : R.elapsed U ≤ t) :
    R.clock t = U + (t - R.elapsed U) := by
  have hu : U ≤ R.clock t := (elapsed_le_clock_iff R U t).mpr ht
  have hi : (∫ u in U..R.clock t, (R.rate u)⁻¹) = R.clock t - U := by
    calc
      _ = ∫ _ in U..R.clock t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu'
        have hu'' : u ∈ Icc U (R.clock t) := by simpa only [uIcc_of_le hu] using hu'
        change (R.rate u)⁻¹ = 1
        rw [hafter u hu''.1, inv_one]
      _ = R.clock t - U := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]
  have heq := R.elapsed_sub U (R.clock t)
  rw [R.elapsed_clock, hi] at heq
  linarith only [heq]

/-- The scalar form of the literal two-particle normalized energy. -/
def scalarEnergy (β q : ℝ) : ℝ := (1 + Real.exp (β * (q - 1))) / 2

theorem scalarEnergy_monotone (β : ℝ) (hβ : 0 ≤ β) : Monotone (scalarEnergy β) := by
  intro p q hpq
  have he : Real.exp (β * (p - 1)) ≤ Real.exp (β * (q - 1)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right hpq 1) hβ)
  dsimp [scalarEnergy]
  linarith only [he]

theorem scalarEnergy_le_one (β q : ℝ) (hβ : 0 ≤ β) (hq : q ≤ 1) :
    scalarEnergy β q ≤ 1 := by
  have he : Real.exp (β * (q - 1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hβ (sub_nonpos.mpr hq))
  dsimp [scalarEnergy]
  linarith only [he]

/-- Post-cutoff energy is bounded between the energy at the cutoff and one.
Together with convergence of cutoff energy to one this gives a uniform tail bound. -/
theorem postcutoff_energy_squeeze (R : BoundedPositiveRate) (β q U : ℝ) (ρ : ℝ → ℝ)
    (hβ : 0 ≤ β) (hU : 0 ≤ U)
    (hupper : ∀ u : ℝ, 0 ≤ u → ρ u ≤ 1)
    (hafter : ∀ u : ℝ, U ≤ u → q ≤ ρ u)
    {t : ℝ} (ht : R.elapsed U ≤ t) :
    scalarEnergy β q ≤ scalarEnergy β (ρ (R.clock t)) ∧
      scalarEnergy β (ρ (R.clock t)) ≤ 1 := by
  have hu := (elapsed_le_clock_iff R U t).mpr ht
  exact ⟨scalarEnergy_monotone β hβ (hafter (R.clock t) hu),
    scalarEnergy_le_one β (ρ (R.clock t)) hβ (hupper (R.clock t) (hU.trans hu))⟩

end Metastability.StoppedEnergy
