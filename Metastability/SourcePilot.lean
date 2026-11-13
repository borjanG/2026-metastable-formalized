import Metastability.SourceTrajectory
import Metastability.PilotTheorem

/-!
# Two-particle USA energy staircase from the source ODE alone

The clocks in this theorem are constructed from the actual cutoff rule. The
only dynamical input is `Source.Solves`; continuity, scalar dynamics, first
cutoff crossing, and energy asymptotics are proved in the imported modules.
No assertion about the full collision-tree theorem is made here.
-/

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace

namespace Metastability.SourcePilot

/-- The two-particle USA pilot with the literal manuscript ODE premise and a constructed clock.
The initial correlation is fixed in `(-1,1)`, and beta ranges over the reals.
Convergence is uniform on every compact set of nonnegative accelerated times
avoiding the jump at `1/2`; the initial time is included. -/
theorem energy_staircase {d : ℕ}
    (X : ℝ → ℝ → Source.Configuration 2 d)
    (hX : ∀ β > 1, Source.Solves .usa β (X β))
    (ρ₀ : ℝ) (hρl : -1 < ρ₀) (hρu : ρ₀ < 1)
    (hinitial : ∀ β > 1, ⟪(X β 0 0).val, (X β 0 1).val⟫ = ρ₀) :
    ∃ clock : ℝ → ℝ → ℝ,
      (∀ β > 1, Source.ClockRelation β (X β) 0 (clock β)) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Ici 0 → (1 / 2 : ℝ) ∉ K →
        TendstoUniformlyOn
          (fun β t => Source.energy β (X β (clock β t)))
          (fun t => if t < 1 / 2 then 1 / 2 else 1) atTop K := by
  let P : PilotTheorem.Family d := fun β hβ =>
    SourceTrajectory.trajectory β (X β) (hX β hβ)
  have hPinitial : ∀ (β : ℝ) (hβ : 1 < β), (P β hβ).correlation 0 = ρ₀ := by
    intro β hβ
    change ⟪((SourceTrajectory.trajectory β (X β) (hX β hβ)).x 0).val,
      ((SourceTrajectory.trajectory β (X β) (hX β hβ)).y 0).val⟫ = ρ₀
    rw [SourceTrajectory.trajectory_x_of_nonneg β (X β) (hX β hβ) (by norm_num),
      SourceTrajectory.trajectory_y_of_nonneg β (X β) (hX β hβ) (by norm_num)]
    exact hinitial β hβ
  refine ⟨PilotTheorem.clock P, ?_, ?_⟩
  · intro β hβ
    have hclock : PilotTheorem.clock P β = (P β hβ).clock hβ := by
      funext t
      simp only [PilotTheorem.clock, dif_pos hβ]
    rw [hclock]
    exact SourceTrajectory.trajectory_clockRelation_source β hβ (X β) (hX β hβ)
  · intro K hK hKsub hjump
    have hlimit := PilotTheorem.energy_staircase P ρ₀ hρl hρu hPinitial hK hKsub hjump
    apply hlimit.congr
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
    intro t ht
    simp only [PilotTheorem.energy, PilotTheorem.clock, dif_pos hβ]
    exact SourceTrajectory.trajectory_energy_eq_source β hβ (X β) (hX β hβ) (hKsub ht)

end Metastability.SourcePilot
