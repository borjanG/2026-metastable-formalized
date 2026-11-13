import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring

/-!
# Exact two-particle identities for unnormalized self-attention

The vector equations below are the manuscript's USA system with `n = 2`.
The scalar law is derived from those vector equations and the unit-norm
conditions; it is not assumed. The accelerated identity is a conditional
chain-rule helper: it requires the stated derivative of the time change at
the point under consideration and does not construct the global clock.
-/

noncomputable section

namespace Metastability.TwoParticle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Orthogonal tangent projection at a unit vector, written on the ambient space. -/
def projection (x y : E) : E :=
  y - inner ℝ x y • x

/-- Velocity of one particle in the two-particle USA system after its zero self-term
has been removed. The unit-norm condition justifying that removal is proved below. -/
def twoParticleVelocity (β : ℝ) (x y : E) : E :=
  ((1 / 2 : ℝ) * Real.exp (β * (inner ℝ x y - 1))) • projection x y

/-- The literal two terms in the manuscript's USA sum for `n = 2`. -/
def twoParticleVelocityWithSelf (β : ℝ) (x y : E) : E :=
  (1 / 2 : ℝ) •
    (Real.exp (β * (inner ℝ x x - 1)) • projection x x +
      Real.exp (β * (inner ℝ x y - 1)) • projection x y)

/-- The manuscript's normalized energy, including both ordered cross terms and
both diagonal terms, specialized to two particles. -/
def twoParticleEnergy (β : ℝ) (x y : E) : ℝ :=
  (Real.exp (β * (inner ℝ x x - 1)) +
    Real.exp (β * (inner ℝ x y - 1)) +
    Real.exp (β * (inner ℝ y x - 1)) +
    Real.exp (β * (inner ℝ y y - 1))) / 4

theorem projection_self_of_norm_eq_one (x : E) (hx : ‖x‖ = 1) :
    projection x x = 0 := by
  simp only [projection, real_inner_self_eq_norm_sq, hx, one_pow, one_smul, sub_self]

theorem inner_projection_of_norm_eq_one (x y : E) (hx : ‖x‖ = 1) :
    inner ℝ x (projection x y) = 0 := by
  simp only [projection, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, hx, one_pow, mul_one, sub_self]

theorem twoParticleVelocityWithSelf_eq (β : ℝ) (x y : E) (hx : ‖x‖ = 1) :
    twoParticleVelocityWithSelf β x y = twoParticleVelocity β x y := by
  simp only [twoParticleVelocityWithSelf, projection_self_of_norm_eq_one x hx,
    smul_zero, zero_add, smul_smul, twoParticleVelocity]

/-- Exact energy reduction on the unit sphere. -/
theorem twoParticleEnergy_eq (β : ℝ) (x y : E)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    twoParticleEnergy β x y =
      (1 + Real.exp (β * (inner ℝ x y - 1))) / 2 := by
  simp only [twoParticleEnergy, real_inner_self_eq_norm_sq, hx, hy, one_pow,
    sub_self, mul_zero, Real.exp_zero, real_inner_comm x y]
  ring

/-- The algebraic calculation underlying the exact scalar equation. -/
theorem scalarVelocity_eq (β : ℝ) (x y : E)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    inner ℝ x (twoParticleVelocity β y x) +
        inner ℝ (twoParticleVelocity β x y) y =
      (1 - (inner ℝ x y) ^ 2) * Real.exp (β * (inner ℝ x y - 1)) := by
  simp only [twoParticleVelocity, projection, real_inner_smul_left,
    real_inner_smul_right, inner_sub_left, inner_sub_right,
    real_inner_self_eq_norm_sq, hx, hy, one_pow, real_inner_comm x y]
  ring

/-- The original-time scalar law follows from the vector USA equations. -/
theorem hasDerivAt_inner (β : ℝ) (x y : ℝ → E) (τ : ℝ)
    (hx : ‖x τ‖ = 1) (hy : ‖y τ‖ = 1)
    (hx' : HasDerivAt x (twoParticleVelocity β (x τ) (y τ)) τ)
    (hy' : HasDerivAt y (twoParticleVelocity β (y τ) (x τ)) τ) :
    HasDerivAt (fun s => inner ℝ (x s) (y s))
      ((1 - (inner ℝ (x τ) (y τ)) ^ 2) *
        Real.exp (β * (inner ℝ (x τ) (y τ) - 1))) τ := by
  have h := hx'.inner ℝ hy'
  rw [scalarVelocity_eq β (x τ) (y τ) hx hy] at h
  exact h

/-- The same scalar law, starting from the full two-term USA vector field. -/
theorem hasDerivAt_inner_of_fullUSA (β : ℝ) (x y : ℝ → E) (τ : ℝ)
    (hx : ‖x τ‖ = 1) (hy : ‖y τ‖ = 1)
    (hx' : HasDerivAt x (twoParticleVelocityWithSelf β (x τ) (y τ)) τ)
    (hy' : HasDerivAt y (twoParticleVelocityWithSelf β (y τ) (x τ)) τ) :
    HasDerivAt (fun s => inner ℝ (x s) (y s))
      ((1 - (inner ℝ (x τ) (y τ)) ^ 2) *
        Real.exp (β * (inner ℝ (x τ) (y τ) - 1))) τ := by
  rw [twoParticleVelocityWithSelf_eq β (x τ) (y τ) hx] at hx'
  rw [twoParticleVelocityWithSelf_eq β (y τ) (x τ) hy] at hy'
  exact hasDerivAt_inner β x y τ hx hy hx' hy'

/-- Attraction: the exact scalar velocity is nonnegative on the unit sphere. -/
theorem scalarVelocity_nonneg (β : ℝ) (x y : E)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    0 ≤ (1 - (inner ℝ x y) ^ 2) * Real.exp (β * (inner ℝ x y - 1)) := by
  have habs : |inner ℝ x y| ≤ 1 := by
    simpa only [hx, hy, mul_one] using abs_real_inner_le_norm x y
  exact mul_nonneg (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr habs))
    (Real.exp_pos _).le

/-- On any convex interval where the unit-norm vector USA equations hold, the
two-particle scalar product is nondecreasing. -/
theorem monotoneOn_inner_of_fullUSA (β : ℝ) (x y : ℝ → E)
    (D : Set ℝ) (hD : Convex ℝ D)
    (hx : ∀ τ ∈ D, ‖x τ‖ = 1) (hy : ∀ τ ∈ D, ‖y τ‖ = 1)
    (hx' : ∀ τ ∈ D,
      HasDerivAt x (twoParticleVelocityWithSelf β (x τ) (y τ)) τ)
    (hy' : ∀ τ ∈ D,
      HasDerivAt y (twoParticleVelocityWithSelf β (y τ) (x τ)) τ) :
    MonotoneOn (fun τ => inner ℝ (x τ) (y τ)) D := by
  have hderiv : ∀ τ ∈ D, HasDerivAt (fun s => inner ℝ (x s) (y s))
      ((1 - (inner ℝ (x τ) (y τ)) ^ 2) *
        Real.exp (β * (inner ℝ (x τ) (y τ) - 1))) τ := by
    intro τ hτ
    exact hasDerivAt_inner_of_fullUSA β x y τ (hx τ hτ) (hy τ hτ)
      (hx' τ hτ) (hy' τ hτ)
  apply monotoneOn_of_deriv_nonneg hD
  · intro τ hτ
    exact (hderiv τ hτ).continuousAt.continuousWithinAt
  · intro τ hτ
    exact (hderiv τ (interior_subset hτ)).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [(hderiv τ (interior_subset hτ)).deriv]
    exact scalarVelocity_nonneg β (x τ) (y τ)
      (hx τ (interior_subset hτ)) (hy τ (interior_subset hτ))

/-- Exact cancellation of the Arrhenius factors. -/
theorem scalar_clock_cancellation (β ρ : ℝ) :
    ((1 - ρ ^ 2) * Real.exp (β * (ρ - 1))) *
        (Real.log β * Real.exp (β * (1 - ρ))) =
      (1 - ρ ^ 2) * Real.log β := by
  have hexp : Real.exp (β * (ρ - 1)) * Real.exp (β * (1 - ρ)) = 1 := by
    rw [← Real.exp_add]
    have hzero : β * (ρ - 1) + β * (1 - ρ) = 0 := by ring
    rw [hzero, Real.exp_zero]
  calc
    _ = ((1 - ρ ^ 2) * Real.log β) *
        (Real.exp (β * (ρ - 1)) * Real.exp (β * (1 - ρ))) := by ring
    _ = (1 - ρ ^ 2) * Real.log β := by rw [hexp, mul_one]

/-- Conditional chain-rule helper for a time change with the active clock rate.
This is local and does not assert existence or differentiability everywhere of
the manuscript's cutoff-dependent global clock. -/
theorem hasDerivAt_inner_comp_activeClock (β : ℝ) (x y : ℝ → E)
    (τ : ℝ → ℝ) (t : ℝ)
    (hx : ‖x (τ t)‖ = 1) (hy : ‖y (τ t)‖ = 1)
    (hx' : HasDerivAt x (twoParticleVelocity β (x (τ t)) (y (τ t))) (τ t))
    (hy' : HasDerivAt y (twoParticleVelocity β (y (τ t)) (x (τ t))) (τ t))
    (hτ : HasDerivAt τ
      (Real.log β * Real.exp (β * (1 - inner ℝ (x (τ t)) (y (τ t))))) t) :
    HasDerivAt (fun s => inner ℝ (x (τ s)) (y (τ s)))
      ((1 - (inner ℝ (x (τ t)) (y (τ t))) ^ 2) * Real.log β) t := by
  have h := (hasDerivAt_inner β x y (τ t) hx hy hx' hy').comp t hτ
  rw [scalar_clock_cancellation] at h
  exact h

end Metastability.TwoParticle
