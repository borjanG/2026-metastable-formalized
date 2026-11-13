import Metastability.TreeCapEnlargement
import Metastability.ActiveLogCoordinate

/-! Entry-cap control of the active logarithmic coordinate. -/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Metastability.ActiveEntry
open Source CapEnlargement ActiveLogCoordinate
variable {n N d : ℕ}

/-- The literal enlarged entry caps keep the initial correlation in a fixed
compact subset of (-1,1), and its logarithmic half-angle is uniformly bounded.
No assertion about a later scalar trajectory is a premise. -/
theorem entry_log_bound (T : CollisionTree n N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) (l : Fin N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ x y : Sphere d,
        angularDist x (C (T.leftNode l)).center ≤
          (C (T.leftNode l)).radius + M * enlargementScale β →
        angularDist y (C (T.rightNode l)).center ≤
          (C (T.rightNode l)).radius + M * enlargementScale β →
        ⟪x.val, y.val⟫ ∈ Ioo (-1 : ℝ) 1 ∧ |logHalfAngle ⟪x.val, y.val⟫| ≤ B := by
  have hl : 0 < lowerBarrier C l := TreeSeparation.lowerBarrier_pos T C hC l
  have hu : upperBarrier C l < 2 := by
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
      (CapDistances.capMaxDistance_nonneg (C (T.leftNode l)) (C (T.rightNode l)))
      (le_refl Real.pi) (hC.2 l).2.2.1
    rw [Real.cos_pi] at hcos
    change 1 - Real.cos (upperAngle C l) < 2
    change -1 < Real.cos (upperAngle C l) at hcos
    linarith only [hcos]
  let δ := min (lowerBarrier C l / 2) ((2 - upperBarrier C l) / 2)
  have hδ : 0 < δ := lt_min (half_pos hl) (half_pos (sub_pos.mpr hu))
  let lo := 1 - upperBarrier C l - δ
  let hi := 1 - lowerBarrier C l + δ
  have hlo : -1 < lo := by
    have h := min_le_right (lowerBarrier C l / 2) ((2 - upperBarrier C l) / 2)
    dsimp only [lo, δ]
    linarith only [h, hu]
  have hhi : hi < 1 := by
    have h := min_le_left (lowerBarrier C l / 2) ((2 - upperBarrier C l) / 2)
    dsimp only [hi, δ]
    linarith only [h, hl]
  have hcont : ContinuousOn logHalfAngle (Icc lo hi) :=
    continuousOn_logHalfAngle.mono (fun _ h => ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨β₀, hβ₀, hfamily⟩ := exists_uniform_enlarged_family C δ hδ
  refine ⟨max B 0, le_max_right _ _, β₀, hβ₀, ?_⟩
  intro β hβ M hM x y hx hy
  obtain ⟨E, hE, herr, hperturb⟩ := hfamily β hβ M hM
  have hxE : x ∈ (E (T.leftNode l)).carrier := by
    change angularDist x (E (T.leftNode l)).center ≤ (E (T.leftNode l)).radius
    rw [(hE _).1, (hE _).2]
    exact hx
  have hyE : y ∈ (E (T.rightNode l)).carrier := by
    change angularDist y (E (T.rightNode l)).center ≤ (E (T.rightNode l)).radius
    rw [(hE _).1, (hE _).2]
    exact hy
  have hmin := min_barrier_le_deficit (E (T.leftNode l)) (E (T.rightNode l)) x y hxE hyE
  have hmax := deficit_le_max_barrier (E (T.leftNode l)) (E (T.rightNode l)) x y hxE hyE
  rw [AngularGeometry.cos_angularDist] at hmin hmax
  have hpl := (hperturb (T.leftNode l) (T.rightNode l)).1
  have hpu := (hperturb (T.leftNode l) (T.rightNode l)).2
  change lowerBarrier C l - 2 * (M * enlargementScale β) ≤ lowerBarrier E l at hpl
  change upperBarrier E l ≤ upperBarrier C l + 2 * (M * enlargementScale β) at hpu
  change lowerBarrier E l ≤ 1 - ⟪x.val, y.val⟫ at hmin
  change 1 - ⟪x.val, y.val⟫ ≤ upperBarrier E l at hmax
  have hmem : ⟪x.val, y.val⟫ ∈ Icc lo hi := by
    dsimp only [lo, hi]
    constructor <;> linarith only [hpl, hpu, hmin, hmax, herr]
  refine ⟨⟨hlo.trans_le hmem.1, hmem.2.trans_lt hhi⟩, ?_⟩
  have hb : |logHalfAngle ⟪x.val, y.val⟫| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB _ hmem
  exact hb.trans (le_max_left _ _)

end Metastability.ActiveEntry
