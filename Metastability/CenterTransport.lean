import Metastability.NextStageGeometry
import Metastability.FiniteTransport

/-! Literal next-partition center targets and their empirical transport bounds. -/
noncomputable section
namespace Metastability.CenterTransport
open Source
variable {n N d : ℕ}

theorem blockOf_succ_of_parent (T : CollisionTree n N) (l : Fin N)
    (p : Fin n) (hp : p ∈ T.parent l) : T.blockOf l.succ p = T.parent l := by
  apply (T.blockOf_unique l.succ p (T.parent l) _ hp).symm
  rw [T.merge l]
  exact Finset.mem_insert_self _ _

theorem blockOf_succ_of_inactive (T : CollisionTree n N) (l : Fin N)
    (D : Block n) (hD : D ∈ T.partition l.castSucc)
    (hDl : D ≠ T.left l) (hDr : D ≠ T.right l) (p : Fin n) (hp : p ∈ D) :
    T.blockOf l.succ p = D := by
  apply (T.blockOf_unique l.succ p D _ hp).symm
  rw [T.merge l]
  exact Finset.mem_insert_of_mem
    (Finset.mem_erase.mpr ⟨hDr, Finset.mem_erase.mpr ⟨hDl, hD⟩⟩)

/-- The weights of both children combine into the literal parent mass because
all labels in their union receive the parent target in the next partition. -/
theorem empirical_next_le (T : CollisionTree n N) (hn : 0 < n)
    (z : NodeCenters T d) (l : Fin N) (x : Configuration n d) (ε : ℝ)
    (hparent : ∀ p ∈ T.parent l, angularDist (x p) (z (T.parent l) (T.parent_node l)) ≤ ε)
    (hinactive : ∀ D (hD : D ∈ T.partition l.castSucc), D ≠ T.left l → D ≠ T.right l →
      ∀ p ∈ D, angularDist (x p) (z D ⟨l.castSucc, hD⟩) ≤ ε) :
    empiricalWasserstein hn x (partitionConfiguration T z l.succ) ≤ ε := by
  apply FiniteTransport.empiricalWasserstein_le_of_pointwise
  intro p
  by_cases hp : p ∈ T.parent l
  · have heq := blockOf_succ_of_parent T l p hp
    simpa only [partitionConfiguration, heq] using hparent p hp
  · let D := T.blockOf l.castSucc p
    have hD := (T.blockOf_spec l.castSucc p).1
    have hpin := (T.blockOf_spec l.castSucc p).2
    have hDl : D ≠ T.left l := by
      intro he
      exact hp (Finset.mem_union_left _ (he ▸ hpin))
    have hDr : D ≠ T.right l := by
      intro he
      exact hp (Finset.mem_union_right _ (he ▸ hpin))
    have heq := blockOf_succ_of_inactive T l D hD hDl hDr p hpin
    simpa only [partitionConfiguration, heq] using hinactive D hD hDl hDr p hpin

theorem partitionConfiguration_final (T : CollisionTree n N) (z : NodeCenters T d) :
    partitionConfiguration T z (Fin.last N) =
      fun _ => z Finset.univ ⟨Fin.last N, by rw [T.final_partition]; exact Finset.mem_singleton_self _⟩ := by
  funext p
  have hblock : T.blockOf (Fin.last N) p = Finset.univ := by
    have hh := (T.blockOf_spec (Fin.last N) p).1
    simpa only [T.final_partition, Finset.mem_singleton] using hh
  simp only [partitionConfiguration, hblock]

end Metastability.CenterTransport
