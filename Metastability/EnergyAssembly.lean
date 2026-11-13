import Metastability.EnergyEstimates
import Metastability.TreePairCounting

/-!
# Source plateau estimates and uniform analytic assembly

The combinatorial plateau is identified with the source tree definition.
Uniform limits below are conditional transfer lemmas: the full dynamical
cascade must supply the geometric error bounds and their beta asymptotics.
-/

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.EnergyAssembly
variable {n N d : ℕ}

theorem pairPlateau_eq_source (T : Source.CollisionTree n N) (l : Fin (N + 1)) :
    EnergyEstimates.pairPlateau (T.blockOf l) = Source.plateauEnergy T l :=
  TreePairCounting.normalized_same_block_pairs T l

/-- Explicit geometric control of the manuscript's plateau energy for any partition. -/
theorem energy_sub_plateau_le (T : Source.CollisionTree n N) (l : Fin (N + 1))
    (β ε L : ℝ) (hβ : 0 ≤ β) (hε : 0 ≤ ε) (x : Source.Configuration n d)
    (hwithin : ∀ D ∈ T.partition l, ∀ i ∈ D, ∀ j ∈ D,
      1 - ⟪(x i).val, (x j).val⟫ ≤ ε)
    (hcross : ∀ D ∈ T.partition l, ∀ E ∈ T.partition l, D ≠ E →
      ∀ i ∈ D, ∀ j ∈ E, L ≤ 1 - ⟪(x i).val, (x j).val⟫) :
    |Source.energy β x - Source.plateauEnergy T l| ≤ β * ε + Real.exp (-β * L) := by
  rw [← pairPlateau_eq_source]
  apply EnergyEstimates.energy_sub_pairPlateau_le (TreeDynamics.particle_pos T) β ε L hβ hε
  · intro i j hij
    apply hwithin (T.blockOf l i) (T.blockOf_spec l i).1 i (T.blockOf_spec l i).2 j
    exact (TreePairCounting.blockOf_eq_iff_mem T l i j).mp hij
  · intro i j hij
    exact hcross (T.blockOf l i) (T.blockOf_spec l i).1
      (T.blockOf l j) (T.blockOf_spec l j).1 hij i (T.blockOf_spec l i).2 j (T.blockOf_spec l j).2

/-- Uniform geometry-to-energy transfer. No compactness is necessary once the
geometric bounds hold uniformly; obtaining them from the ODE remains separate. -/
theorem tendstoUniformlyOn_plateau_of_geometry (T : Source.CollisionTree n N)
    (l : Fin (N + 1)) (Y : ℝ → ℝ → Source.Configuration n d) (K : Set ℝ)
    (ε L : ℝ → ℝ)
    (herror : Tendsto (fun β : ℝ => β * ε β + Real.exp (-β * L β)) atTop (𝓝 0))
    (hgeometry : ∀ᶠ β : ℝ in atTop, 0 ≤ ε β ∧ ∀ t ∈ K,
      (∀ D ∈ T.partition l, ∀ i ∈ D, ∀ j ∈ D,
        1 - ⟪(Y β t i).val, (Y β t j).val⟫ ≤ ε β) ∧
      (∀ D ∈ T.partition l, ∀ E ∈ T.partition l, D ≠ E →
        ∀ i ∈ D, ∀ j ∈ E, L β ≤ 1 - ⟪(Y β t i).val, (Y β t j).val⟫)) :
    TendstoUniformlyOn (fun β t => Source.energy β (Y β t))
      (fun _ => Source.plateauEnergy T l) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  filter_upwards [hgeometry, eventually_ge_atTop (0 : ℝ), herror.eventually (gt_mem_nhds hδ)]
    with β hg hb he
  intro t ht
  rw [Real.dist_eq, abs_sub_comm]
  exact (energy_sub_plateau_le T l β (ε β) (L β) hb hg.1 (Y β t)
    (hg.2 t ht).1 (hg.2 t ht).2).trans_lt he

end Metastability.EnergyAssembly
