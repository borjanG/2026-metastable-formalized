import Metastability.CascadeFamilyData
import Metastability.StageEnergy
import Metastability.TerminalCompletion
import Metastability.CascadeEnergyTransfer

/-! Global energy convergence for the actual source family. The conditional
assembly theorem consumes geometric data whose source producer is proved;
the final exports assume only the source ODE and visible preparation. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Metastability.GlobalEnergy
open Source CascadeStep
variable {n N d : ℕ}

/-- Reusable energy assembly on a specified, already produced cascade. This
preserves its clock for combination with the measure limit. -/
theorem energy_limit_of_cascade (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ)
    (model : Model) (CStar : ℝ) (hCStar : 0 ≤ CStar)
    (X : ℝ → ℝ → Configuration n d)
    (hX : ∀ β : ℝ, 1 < β → Solves model β (X β))
    (data : CascadeFamilyData T hN C κ model CStar X)
    (K : Set ℝ) (hK : IsCompact K) (hK0 : K ⊆ Ici 0)
    (havoid : ∀ t ∈ K, ∀ l : Fin N, t ≠ jumpTime model T l.succ) :
    TendstoUniformlyOn
      (fun β t => energy β (accelerated (X β) (CStar * β) (data.clock β) t))
      (staircase model T) atTop K := by
  have hstage : ∀ᶠ β : ℝ in atTop, ∀ l : Fin N,
      ∀ t ∈ Icc (data.s β l.castSucc) (data.hit β l),
      |energy β (accelerated (X β) (CStar * β) (data.clock β) t) -
        plateauEnergy T l.castSucc| ≤ StageEnergy.error κ β := by
    filter_upwards [StageEnergy.eventual_energy_bound T hN C hC κ hκ,
      data.stage_times, data.stage_geometry, data.prehit_angle] with β he htimes hgeo hangle
    intro l t ht
    have hM := entryMultiplier_bounds l
    have hM' : entryMultiplier l + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) :=
      ⟨by linarith only [hM.1], by linarith only [hM.2]⟩
    exact he.2 _ hM' l _ (hgeo l t ⟨ht.1, ht.2.trans (htimes l).2.1⟩).1
      (data.i l) (data.j l) (data.i_mem l) (data.j_mem l) (hangle l t ht)
  have hterminal : ∀ᶠ β : ℝ in atTop, ∀ t ≥ data.s β (Fin.last N),
      |energy β (accelerated (X β) (CStar * β) (data.clock β) t) - 1| ≤
        2 * β * clockCutoff β ^ 2 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), TerminalEnergy.eventually_clockCutoff_small,
      data.entry_nonneg, data.final_cutoff] with β hβ hcut hs hcomplete
    intro t ht
    exact (TerminalCompletion.after_completion (T.particle_pos hN) model β hβ hcut.2
      (X β) (hX β hβ) (CStar * β) (mul_nonneg hCStar (zero_lt_one.trans hβ).le)
      (data.clock β) (data.clock_relation β hβ) (data.s β (Fin.last N))
      (hs _) hcomplete t ht).2.1
  have hbound := CascadeEnergyTransfer.uniform_staircase_of_windows T hN model
    (fun β t => energy β (accelerated (X β) (CStar * β) (data.clock β) t))
    (fun β l => data.s β l.castSucc) data.hit (fun β => data.s β (Fin.last N))
    (StageEnergy.error κ) (fun β => 2 * β * clockCutoff β ^ 2)
    (StageEnergy.tendsto_error κ hκ) TerminalEnergy.tendsto_terminal_cap_error
    (fun l => data.entry_tendsto l.castSucc) data.hit_tendsto
    (data.entry_tendsto (Fin.last N)) data.entry_zero hstage hterminal K hK hK0 havoid
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hbound ε hε] with β hh t ht
  rw [Real.dist_eq, abs_sub_comm]
  exact hh t ht

/-- The source energy limit for any common preparation multiplier satisfying
its proved tightening margin. All dynamical stage estimates are produced. -/
theorem global_energy_at_multiplier (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ)
    (hκ : PlateauStability.kappaThreshold n < κ) (model : Model) (CStar : ℝ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar)
    (X : ℝ → ℝ → Configuration n d)
    (hX : ∀ β : ℝ, 1 < β → Solves model β (X β))
    (hvisible : ∀ β : ℝ, 1 < β → VisiblePrepared hN C β (X β 0)) :
    ∃ clock : ℝ → ℝ → ℝ,
      (∀ β : ℝ, 1 < β → ClockRelation β (X β) (CStar * β) (clock β)) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Ici 0 →
        (∀ t ∈ K, ∀ l : Fin N, t ≠ jumpTime model T l.succ) →
        TendstoUniformlyOn
          (fun β t => energy β (accelerated (X β) (CStar * β) (clock β) t))
          (staircase model T) atTop K := by
  obtain ⟨data⟩ := CascadeFamilyData.exists_data T hN C hC κ hκ model CStar hCStar X hX hvisible
  have hκ0 : 0 < κ := (by norm_num : (0 : ℝ) < 4).trans
    ((PlateauStability.kappaThreshold_gt_four n).trans hκ)
  have hCStar0 : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ0)
    (BlockContraction.contraction_constant_pos n (T.particle_pos hN))).trans hCStar
  exact ⟨data.clock, data.clock_relation,
    energy_limit_of_cascade T hN C hC κ hκ0 model CStar hCStar0.le X hX data⟩

/-- Full source-family energy convergence. A single positive shift multiplier
is chosen using only the particle count, before the tree, caps, model, and
family. Beta is real, and the literal source clock exists for every beta > 1. -/
theorem global_energy (n : ℕ) (hn : 0 < n) :
    ∃ CStar : ℝ, 0 < CStar ∧ ∀ (N d : ℕ) (T : CollisionTree n N) (hN : 0 < N)
      (C : TreeCaps T d), StrictlyPrepared C → ∀ model : Model,
      ∀ X : ℝ → ℝ → Configuration n d,
      (∀ β : ℝ, 1 < β → Solves model β (X β)) →
      (∀ β : ℝ, 1 < β → VisiblePrepared hN C β (X β 0)) →
      ∃ clock : ℝ → ℝ → ℝ,
        (∀ β : ℝ, 1 < β → ClockRelation β (X β) (CStar * β) (clock β)) ∧
        ∀ K : Set ℝ, IsCompact K → K ⊆ Ici 0 →
          (∀ t ∈ K, ∀ l : Fin N, t ≠ jumpTime model T l.succ) →
          TendstoUniformlyOn
            (fun β t => energy β (accelerated (X β) (CStar * β) (clock β) t))
            (staircase model T) atTop K := by
  obtain ⟨κ, CStar, hκ, hCStar, hmargin⟩ := GeometricCascade.admissible_parameters n hn
  refine ⟨CStar, hCStar, ?_⟩
  intro N d T hN C hC model X hX hvisible
  exact global_energy_at_multiplier T hN C hC κ hκ model CStar hmargin X hX hvisible

end Metastability.GlobalEnergy
