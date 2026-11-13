import Metastability.CapInvariance
import Metastability.PilotGeometry

/-!
# Uniform terminal energy after containment at the source cutoff

This transfer theorem starts from an explicitly supplied eventual completion
containment condition for actual source ODE solutions. It proves confinement
and energy control at every later original time. It does not prove that the
cascade reaches such a completion time or identify its accelerated location.
The model is fixed but may be either SA or USA, and beta remains real.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace Metastability.TerminalEnergy

variable {n d : ℕ} {model : Source.Model}

/-- The source cutoff eventually defines a strict-hemisphere cap. -/
theorem eventually_clockCutoff_small :
    ∀ᶠ β : ℝ in atTop, 0 < Source.clockCutoff β ∧ Source.clockCutoff β < Real.pi / 2 := by
  simpa only [PilotGeometry.clockCutoff_eq_angularCutoff] using
    PilotCutoff.eventually_angularCutoff_small

/-- The terminal cap error vanishes for the exact source cutoff. -/
theorem tendsto_terminal_cap_error :
    Tendsto (fun β : ℝ => 2 * β * Source.clockCutoff β ^ 2) atTop (𝓝 0) := by
  simpa only [PilotGeometry.clockCutoff_eq_angularCutoff, mul_assoc, mul_zero] using
    PilotCutoff.tendsto_beta_mul_angularCutoff_sq.const_mul (2 : ℝ)

/-- Actual source solutions trapped at completion satisfy the terminal energy
bound uniformly over the entire unbounded interval of subsequent original times. -/
theorem eventually_energy_bound (hn : 0 < n)
    (X : ℝ → ℝ → Source.Configuration n d)
    (hX : ∀ β > 1, Source.Solves model β (X β))
    (a : ℝ → ℝ) (ha : ∀ β > 1, 0 ≤ a β) (p : ℝ → Source.Sphere d)
    (hcompletion : ∀ᶠ β : ℝ in atTop, ∀ i,
      Source.angularDist (X β (a β) i) (p β) ≤ Source.clockCutoff β) :
    ∀ᶠ β : ℝ in atTop, ∀ u, a β ≤ u →
      0 ≤ 1 - Source.energy β (X β u) ∧
        1 - Source.energy β (X β u) ≤ 2 * β * Source.clockCutoff β ^ 2 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_clockCutoff_small, hcompletion]
    with β hβ hcut hcomp
  let C : Source.SphericalCap d := ⟨p β, Source.clockCutoff β, hcut.1.le, hcut.2⟩
  exact CapInvariance.full_cap_energy_bound hn (by linarith only [hβ])
    (X β) (hX β hβ) C (a β) (ha β hβ) hcomp

/-- Uniform convergence to the terminal plateau for every later original time.
Completion containment is an input here; it is a separate dynamical obligation
of the full cascade proof. No convergence of the completion centers is needed. -/
theorem uniform_terminal_energy (hn : 0 < n)
    (X : ℝ → ℝ → Source.Configuration n d)
    (hX : ∀ β > 1, Source.Solves model β (X β))
    (a : ℝ → ℝ) (ha : ∀ β > 1, 0 ≤ a β) (p : ℝ → Source.Sphere d)
    (hcompletion : ∀ᶠ β : ℝ in atTop, ∀ i,
      Source.angularDist (X β (a β) i) (p β) ≤ Source.clockCutoff β) :
    ∀ δ > 0, ∀ᶠ β : ℝ in atTop, ∀ u, a β ≤ u →
      |Source.energy β (X β u) - 1| < δ := by
  intro δ hδ
  have hsmall := tendsto_terminal_cap_error.eventually (gt_mem_nhds hδ)
  filter_upwards [eventually_energy_bound hn X hX a ha p hcompletion, hsmall]
    with β hbound herror
  intro u hu
  obtain ⟨hlo, hhi⟩ := hbound u hu
  rw [abs_sub_comm, abs_of_nonneg hlo]
  exact hhi.trans_lt herror

end Metastability.TerminalEnergy
