import Metastability.TwoParticle
import Metastability.ScalarClock
import Metastability.PilotAsymptotics

/-!
# Connecting the vector ODE to the explicit pre-cutoff profile

This module proves a stage identity from the actual vector equations and the
active time-change equation. It is not a construction of the cutoff clock or a
claim that the global pilot has been completed.
-/

noncomputable section
open Set

namespace Metastability.Pilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact pre-cutoff correlation profile. The interval hypotheses explicitly
describe an active-clock stage; they are not premises of the final theorem. -/
theorem correlation_eq_profile (β a T : ℝ) (hβ : 1 < β)
    (x y : ℝ → E) (τ : ℝ → ℝ)
    (hx : ∀ t ∈ Icc 0 T, ‖x (τ t)‖ = 1)
    (hy : ∀ t ∈ Icc 0 T, ‖y (τ t)‖ = 1)
    (hx' : ∀ t ∈ Icc 0 T, HasDerivAt x
      (TwoParticle.twoParticleVelocityWithSelf β (x (τ t)) (y (τ t))) (τ t))
    (hy' : ∀ t ∈ Icc 0 T, HasDerivAt y
      (TwoParticle.twoParticleVelocityWithSelf β (y (τ t)) (x (τ t))) (τ t))
    (hτ : ∀ t ∈ Icc 0 T, HasDerivAt τ
      (Real.log β * Real.exp (β * (1 - inner ℝ (x (τ t)) (y (τ t))))) t)
    (hstart : -1 < inner ℝ (x (τ 0)) (y (τ 0)))
    (ha : ScalarClock.odds (inner ℝ (x (τ 0)) (y (τ 0))) = a ^ 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    inner ℝ (x (τ t)) (y (τ t)) = PilotAsymptotics.cosineProfile a β t := by
  let ρ : ℝ → ℝ := fun s => inner ℝ (x (τ s)) (y (τ s))
  have hd : ∀ s ∈ Icc 0 T, HasDerivAt ρ ((1 - ρ s ^ 2) * Real.log β) s := by
    intro s hs
    have hxv := hx' s hs
    have hyv := hy' s hs
    rw [TwoParticle.twoParticleVelocityWithSelf_eq β _ _ (hx s hs)] at hxv
    rw [TwoParticle.twoParticleVelocityWithSelf_eq β _ _ (hy s hs)] at hyv
    exact TwoParticle.hasDerivAt_inner_comp_activeClock β x y τ s
      (hx s hs) (hy s hs) hxv hyv (hτ s hs)
  have hmono : MonotoneOn ρ (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      have hi : |ρ s| ≤ 1 := by
        simpa only [ρ, hx s (interior_subset hs), hy s (interior_subset hs), mul_one]
          using abs_real_inner_le_norm (x (τ s)) (y (τ s))
      exact mul_nonneg (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr hi))
        (Real.log_pos hβ).le
  have hne : ∀ s ∈ Icc 0 T, 1 + ρ s ≠ 0 := by
    intro s hs
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hs.1.trans hs.2⟩
    have hle := hmono h0 hs hs.1
    have hstart' : -1 < ρ 0 := hstart
    linarith
  have ho := ScalarClock.odds_eq_initial_mul_exp hd hne ht
  have hpow : Real.exp (-(2 * Real.log β * t)) = β ^ (-2 * t) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < β)]
    congr 1
    ring
  rw [ha, hpow, ← PilotAsymptotics.halfAngle_sq a β t (by linarith : 0 ≤ β)] at ho
  exact ScalarClock.correlation_of_odds (hne t ht) (by positivity) ho

/-- The literal four-term particle energy equals the analytic profile on an
active-clock interval, with all scalar equations derived from the vector ODE. -/
theorem energy_eq_profile (β a T : ℝ) (hβ : 1 < β)
    (x y : ℝ → E) (τ : ℝ → ℝ)
    (hx : ∀ t ∈ Icc 0 T, ‖x (τ t)‖ = 1)
    (hy : ∀ t ∈ Icc 0 T, ‖y (τ t)‖ = 1)
    (hx' : ∀ t ∈ Icc 0 T, HasDerivAt x
      (TwoParticle.twoParticleVelocityWithSelf β (x (τ t)) (y (τ t))) (τ t))
    (hy' : ∀ t ∈ Icc 0 T, HasDerivAt y
      (TwoParticle.twoParticleVelocityWithSelf β (y (τ t)) (x (τ t))) (τ t))
    (hτ : ∀ t ∈ Icc 0 T, HasDerivAt τ
      (Real.log β * Real.exp (β * (1 - inner ℝ (x (τ t)) (y (τ t))))) t)
    (hstart : -1 < inner ℝ (x (τ 0)) (y (τ 0)))
    (ha : ScalarClock.odds (inner ℝ (x (τ 0)) (y (τ 0))) = a ^ 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    TwoParticle.twoParticleEnergy β (x (τ t)) (y (τ t)) =
      PilotAsymptotics.analyticEnergy a β t := by
  rw [TwoParticle.twoParticleEnergy_eq β _ _ (hx t ht) (hy t ht),
    correlation_eq_profile β a T hβ x y τ hx hy hx' hy' hτ hstart ha ht]
  unfold PilotAsymptotics.analyticEnergy PilotAsymptotics.arrheniusExponent
    PilotAsymptotics.cosineProfile
  congr 2
  congr 1
  have hne : 1 + (PilotAsymptotics.halfAngle a β t) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Metastability.Pilot
