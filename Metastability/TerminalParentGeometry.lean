import Metastability.ActiveClock

/-! The actual parent-completion cutoff and a selected representative angle. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Metastability.TerminalParentGeometry
open Source
variable {n N d : ℕ}

theorem representative_gt_half_cutoff_of_noncomplete (T : CollisionTree n N) (l : Fin N)
    (β ε : ℝ) (hβ : 1 < β) (x : Configuration n d)
    (htight : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) ≤ ε) (hε : ε ≤ clockCutoff β / 4)
    (i j : Fin n) (hi : i ∈ T.left l) (hj : j ∈ T.right l)
    (hparent : ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (x p) (x q) ≤ clockCutoff β) :
    clockCutoff β / 2 < angularDist (x i) (x j) := by
  have hε' : ε ≤ clockCutoff β := by
    linarith only [hε, ActiveScales.clockCutoff_pos hβ]
  obtain ⟨p, q, hpq, helig⟩ :=
    ActiveClock.eligible_active_of_parent_not_complete T l β ε x htight hε' hparent
  have hangle := ((ActiveClock.mem_eligiblePairs β x p q).mp helig).2
  have hnear := (abs_le.mp (ActiveClock.activeCross_angle_error T l ε x htight i j hi hj p q hpq)).2
  linarith only [hangle, hnear, hε]

theorem parent_complete_of_representative_le_half_cutoff (T : CollisionTree n N) (l : Fin N)
    (β ε : ℝ) (hβ : 1 < β) (x : Configuration n d)
    (htight : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) ≤ ε) (hε : ε ≤ clockCutoff β / 4)
    (i j : Fin n) (hi : i ∈ T.left l) (hj : j ∈ T.right l)
    (hangle : angularDist (x i) (x j) ≤ clockCutoff β / 2) :
    ∀ p ∈ T.parent l, ∀ q ∈ T.parent l, angularDist (x p) (x q) ≤ clockCutoff β := by
  by_contra hparent
  exact (not_lt_of_ge hangle)
    (representative_gt_half_cutoff_of_noncomplete T l β ε hβ x htight hε i j hi hj hparent)

end Metastability.TerminalParentGeometry
