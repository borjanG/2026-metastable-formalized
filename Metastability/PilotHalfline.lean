import Metastability.Pilot

/-!
# Active-stage integration with half-line and cutoff endpoints

These conditional helpers require the differential equations only in the
interior of an active stage. Continuity supplies both endpoints, including the
clock cutoff where a classical derivative of the clock need not exist.
The vector helpers use original-time ODE derivatives only at positive times.
-/

noncomputable section
open Set

namespace Metastability.PilotHalfline

/-- Integrate the logistic correlation equation using only interior derivatives.
The closed-interval continuity hypothesis carries the identity to the cutoff. -/
theorem odds_eq_initial_mul_exp {ρ : ℝ → ℝ} {T c : ℝ}
    (hc : ContinuousOn ρ (Icc 0 T))
    (hρ : ∀ t ∈ Ioo 0 T, HasDerivAt ρ ((1 - ρ t ^ 2) * c) t)
    (hne : ∀ t ∈ Icc 0 T, 1 + ρ t ≠ 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ScalarClock.odds (ρ t) =
      ScalarClock.odds (ρ 0) * Real.exp (-(2 * c * t)) := by
  let f : ℝ → ℝ := fun s => ScalarClock.odds (ρ s) * Real.exp (2 * c * s)
  have hfc : ContinuousOn f (Icc 0 T) := by
    apply ContinuousOn.mul
    · exact (continuousOn_const.sub hc).div (continuousOn_const.add hc) hne
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hfd : ∀ s ∈ interior (Icc 0 T), HasDerivAt f 0 s := by
    intro s hs
    have hs' : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
    exact ScalarClock.hasDerivAt_weighted_odds (hρ s hs') (hne s (Ioo_subset_Icc_self hs'))
  have hmono : MonotoneOn f (Icc 0 T) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hfc
      (fun s hs => (hfd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => by rw [(hfd s hs).deriv])
  have hanti : AntitoneOn f (Icc 0 T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hfc
      (fun s hs => (hfd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => by rw [(hfd s hs).deriv])
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hi : f t = f 0 :=
    le_antisymm (hanti h0 ht ht.1) (hmono h0 ht ht.1)
  simp only [f, mul_zero, Real.exp_zero, mul_one] at hi
  calc
    ScalarClock.odds (ρ t) =
        (ScalarClock.odds (ρ t) * Real.exp (2 * c * t)) *
          Real.exp (-(2 * c * t)) := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ = ScalarClock.odds (ρ 0) * Real.exp (-(2 * c * t)) := by rw [hi]

/-- The scalar profile includes the stage endpoint, without assuming a
derivative there. This is a helper whose scalar hypotheses are explicit. -/
theorem correlation_eq_profile_of_logistic (β a T : ℝ) (hβ : 1 < β)
    (ρ : ℝ → ℝ) (hc : ContinuousOn ρ (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt ρ ((1 - ρ t ^ 2) * Real.log β) t)
    (hbound : ∀ t ∈ Icc 0 T, |ρ t| ≤ 1)
    (hstart : -1 < ρ 0) (ha : ScalarClock.odds (ρ 0) = a ^ 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ρ t = PilotAsymptotics.cosineProfile a β t := by
  have hmono : MonotoneOn ρ (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hc
    · intro s hs
      have hs' : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
      exact (hd s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
      rw [(hd s hs').deriv]
      exact mul_nonneg
        (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr (hbound s (interior_subset hs))))
        (Real.log_pos hβ).le
  have hne : ∀ s ∈ Icc 0 T, 1 + ρ s ≠ 0 := by
    intro s hs
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hs.1.trans hs.2⟩
    have hle := hmono h0 hs hs.1
    linarith
  have ho := odds_eq_initial_mul_exp hc hd hne ht
  have hpow : Real.exp (-(2 * Real.log β * t)) = β ^ (-2 * t) := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < β)]
    congr 1
    ring
  rw [ha, hpow, ← PilotAsymptotics.halfAngle_sq a β t (by linarith : 0 ≤ β)] at ho
  exact ScalarClock.correlation_of_odds (hne t ht) (by positivity) ho

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual vector USA equations imply the profile on the closed active
stage. Original-time differentiability is used only for `u > 0`, and clock
differentiability only for `0 < t < T`. -/
theorem correlation_eq_profile (β a T : ℝ) (hβ : 1 < β)
    (x y : ℝ → E) (τ : ℝ → ℝ)
    (hxc : ContinuousOn x (Ici 0)) (hyc : ContinuousOn y (Ici 0))
    (hτc : ContinuousOn τ (Icc 0 T))
    (hτ0 : τ 0 = 0) (hτmono : StrictMonoOn τ (Ici 0))
    (hx : ∀ u ∈ Ici (0 : ℝ), ‖x u‖ = 1)
    (hy : ∀ u ∈ Ici (0 : ℝ), ‖y u‖ = 1)
    (hx' : ∀ u > 0, HasDerivAt x
      (TwoParticle.twoParticleVelocityWithSelf β (x u) (y u)) u)
    (hy' : ∀ u > 0, HasDerivAt y
      (TwoParticle.twoParticleVelocityWithSelf β (y u) (x u)) u)
    (hτ : ∀ t ∈ Ioo 0 T, HasDerivAt τ
      (Real.log β * Real.exp (β * (1 - inner ℝ (x (τ t)) (y (τ t))))) t)
    (hstart : -1 < inner ℝ (x 0) (y 0))
    (ha : ScalarClock.odds (inner ℝ (x 0) (y 0)) = a ^ 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    inner ℝ (x (τ t)) (y (τ t)) = PilotAsymptotics.cosineProfile a β t := by
  let ρ : ℝ → ℝ := fun s => inner ℝ (x (τ s)) (y (τ s))
  have hτnonneg : ∀ s ∈ Ici (0 : ℝ), 0 ≤ τ s := by
    intro s hs
    have h := hτmono.monotoneOn (show (0 : ℝ) ∈ Ici 0 by simp) hs hs
    rwa [hτ0] at h
  have hτmaps : MapsTo τ (Icc 0 T) (Ici 0) :=
    fun s hs => hτnonneg s hs.1
  have hc : ContinuousOn ρ (Icc 0 T) :=
    (hxc.comp hτc hτmaps).inner (hyc.comp hτc hτmaps)
  have hd : ∀ s ∈ Ioo 0 T,
      HasDerivAt ρ ((1 - ρ s ^ 2) * Real.log β) s := by
    intro s hs
    have hτpos : 0 < τ s := by
      have h := hτmono (show (0 : ℝ) ∈ Ici 0 by simp) (show s ∈ Ici 0 from hs.1.le) hs.1
      rwa [hτ0] at h
    have hxv := hx' (τ s) hτpos
    have hyv := hy' (τ s) hτpos
    rw [TwoParticle.twoParticleVelocityWithSelf_eq β _ _ (hx (τ s) hτpos.le)] at hxv
    rw [TwoParticle.twoParticleVelocityWithSelf_eq β _ _ (hy (τ s) hτpos.le)] at hyv
    exact TwoParticle.hasDerivAt_inner_comp_activeClock β x y τ s
      (hx (τ s) hτpos.le) (hy (τ s) hτpos.le) hxv hyv (hτ s hs)
  have hbound : ∀ s ∈ Icc 0 T, |ρ s| ≤ 1 := by
    intro s hs
    simpa only [ρ, hx (τ s) (hτmaps hs), hy (τ s) (hτmaps hs), mul_one]
      using abs_real_inner_le_norm (x (τ s)) (y (τ s))
  have hstart' : -1 < ρ 0 := by simpa only [ρ, hτ0] using hstart
  have ha' : ScalarClock.odds (ρ 0) = a ^ 2 := by simpa only [ρ, hτ0] using ha
  exact correlation_eq_profile_of_logistic β a T hβ ρ hc hd hbound hstart' ha' ht

/-- The literal particle energy equals the analytic profile up to and including
the cutoff, with no derivative requirement at the initial or terminal endpoint. -/
theorem energy_eq_profile (β a T : ℝ) (hβ : 1 < β)
    (x y : ℝ → E) (τ : ℝ → ℝ)
    (hxc : ContinuousOn x (Ici 0)) (hyc : ContinuousOn y (Ici 0))
    (hτc : ContinuousOn τ (Icc 0 T))
    (hτ0 : τ 0 = 0) (hτmono : StrictMonoOn τ (Ici 0))
    (hx : ∀ u ∈ Ici (0 : ℝ), ‖x u‖ = 1)
    (hy : ∀ u ∈ Ici (0 : ℝ), ‖y u‖ = 1)
    (hx' : ∀ u > 0, HasDerivAt x
      (TwoParticle.twoParticleVelocityWithSelf β (x u) (y u)) u)
    (hy' : ∀ u > 0, HasDerivAt y
      (TwoParticle.twoParticleVelocityWithSelf β (y u) (x u)) u)
    (hτ : ∀ t ∈ Ioo 0 T, HasDerivAt τ
      (Real.log β * Real.exp (β * (1 - inner ℝ (x (τ t)) (y (τ t))))) t)
    (hstart : -1 < inner ℝ (x 0) (y 0))
    (ha : ScalarClock.odds (inner ℝ (x 0) (y 0)) = a ^ 2)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    TwoParticle.twoParticleEnergy β (x (τ t)) (y (τ t)) =
      PilotAsymptotics.analyticEnergy a β t := by
  have hτnonneg : 0 ≤ τ t := by
    have h := hτmono.monotoneOn (show (0 : ℝ) ∈ Ici 0 by simp)
      (show t ∈ Ici 0 from ht.1) ht.1
    rwa [hτ0] at h
  rw [TwoParticle.twoParticleEnergy_eq β _ _ (hx _ hτnonneg) (hy _ hτnonneg),
    correlation_eq_profile β a T hβ x y τ hxc hyc hτc hτ0 hτmono
      hx hy hx' hy' hτ hstart ha ht]
  unfold PilotAsymptotics.analyticEnergy PilotAsymptotics.arrheniusExponent
    PilotAsymptotics.cosineProfile
  congr 2
  congr 1
  have hne : 1 + (PilotAsymptotics.halfAngle a β t) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Metastability.PilotHalfline
