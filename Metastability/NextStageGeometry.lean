import Metastability.ActiveSourceLaw

/-! The exact merge rule transfers completed-parent geometry to every block
of the next partition. No root cap is introduced. -/
noncomputable section
open Set
namespace Metastability.NextStageGeometry
open Source CapEnlargement ActiveSourceLaw
variable {n N d : ℕ}

theorem next_block_cases (T : CollisionTree n N) (l k : Fin N)
    (hk : k.castSucc = l.succ) (D : Block n) (hD : D ∈ T.partition k.castSucc) :
    D = T.parent l ∨ (D ∈ T.partition l.castSucc ∧ D ≠ T.left l ∧ D ≠ T.right l) := by
  classical
  rw [hk, T.merge l] at hD
  rcases Finset.mem_insert.mp hD with hp | hD
  · exact Or.inl hp
  · obtain ⟨hr, hl, hD⟩ := Finset.mem_erase.mp hD |>.imp_right Finset.mem_erase.mp
    exact Or.inr ⟨hD, hl, hr⟩

theorem completed_partition (T : CollisionTree n N) (C : TreeCaps T d)
    (l k : Fin N) (hk : k.castSucc = l.succ) (β κ M : ℝ) (x : Configuration n d)
    (hstage : StageHyp T C β κ M l x)
    (hsmall : Real.exp (-κ * β) ≤ clockCutoff β)
    (hcomplete : ∀ p ∈ T.parent l, ∀ q ∈ T.parent l, angularDist (x p) (x q) ≤ clockCutoff β) :
    (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) ≤ clockCutoff β) ∧
    (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
      angularDist (x p) (C (T.currentNode k D hD)).center ≤
        (C (T.currentNode k D hD)).radius + M * enlargementScale β) := by
  constructor
  · intro D hD p hp q hq
    rcases next_block_cases T l k hk D hD with rfl | ⟨hD', _, _⟩
    · exact hcomplete p hp q hq
    · exact (hstage.1 D hD' p hp q hq).trans hsmall
  · intro D hD p hp
    rcases next_block_cases T l k hk D hD with rfl | ⟨hD', hl, hr⟩
    · exact hstage.2.2 (T.current_block_proper k _ hD) p hp
    · exact hstage.2.1 D hD' hl hr p hp

end Metastability.NextStageGeometry
