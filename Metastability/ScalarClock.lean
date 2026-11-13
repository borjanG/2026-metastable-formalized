import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Scalar integration for the two-particle pilot

These are analytic helper lemmas. The scalar differential equation is derived
from the actual particle equations in `TwoParticle`; it is not an assumption of
the eventual source-facing metastability theorem.

The odds `(1 - ρ) / (1 + ρ)` equal the squared half-angle tangent. Working with
odds avoids differentiating `arccos` at the ends of its domain.
-/

noncomputable section
open Set

namespace Metastability.ScalarClock

/-- Squared half-angle tangent in correlation coordinates, for `ρ ≠ -1`. -/
def odds (ρ : ℝ) : ℝ := (1 - ρ) / (1 + ρ)

theorem hasDerivAt_odds {ρ : ℝ → ℝ} {t c : ℝ}
    (hρ : HasDerivAt ρ ((1 - ρ t ^ 2) * c) t)
    (hne : 1 + ρ t ≠ 0) :
    HasDerivAt (fun s => odds (ρ s)) (-2 * c * odds (ρ t)) t := by
  convert (hρ.const_sub 1).div (hρ.const_add 1) hne using 1
  dsimp [odds]
  field_simp
  ring

theorem hasDerivAt_weighted_odds {ρ : ℝ → ℝ} {t c : ℝ}
    (hρ : HasDerivAt ρ ((1 - ρ t ^ 2) * c) t)
    (hne : 1 + ρ t ≠ 0) :
    HasDerivAt (fun s => odds (ρ s) * Real.exp (2 * c * s)) 0 t := by
  convert (hasDerivAt_odds hρ hne).mul
    (((hasDerivAt_id t).const_mul (2 * c)).exp) using 1
  ring

/-- Exact integration on a closed interval. This applies with `c = log β`
on any pre-cutoff accelerated interval after deriving the scalar law. -/
theorem odds_eq_initial_mul_exp {ρ : ℝ → ℝ} {T c : ℝ}
    (hρ : ∀ t ∈ Icc 0 T, HasDerivAt ρ ((1 - ρ t ^ 2) * c) t)
    (hne : ∀ t ∈ Icc 0 T, 1 + ρ t ≠ 0)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    odds (ρ t) = odds (ρ 0) * Real.exp (-(2 * c * t)) := by
  have hd : ∀ s ∈ Icc 0 T,
      HasDerivAt (fun u => odds (ρ u) * Real.exp (2 * c * u)) 0 s :=
    fun s hs => hasDerivAt_weighted_odds (hρ s hs) (hne s hs)
  have hc : ContinuousOn (fun u => odds (ρ u) * Real.exp (2 * c * u)) (Icc 0 T) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hi := constant_of_has_deriv_right_zero hc
    (fun s hs => (hd s (mem_Icc_of_Ico hs)).hasDerivWithinAt) t ht
  simp only [mul_zero, Real.exp_zero, mul_one] at hi
  calc
    odds (ρ t) = (odds (ρ t) * Real.exp (2 * c * t)) *
        Real.exp (-(2 * c * t)) := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    _ = odds (ρ 0) * Real.exp (-(2 * c * t)) := by rw [hi]

theorem correlation_of_odds {ρ w : ℝ} (hρ : 1 + ρ ≠ 0)
    (hw : 1 + w ≠ 0) (h : odds ρ = w) :
    ρ = (1 - w) / (1 + w) := by
  rw [odds, div_eq_iff hρ] at h
  apply (eq_div_iff hw).2
  nlinarith [h]

end Metastability.ScalarClock
