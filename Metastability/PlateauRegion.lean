import Metastability.PlateauBootstrap
import Metastability.ActiveSourceLaw

/-! A finite family of literal continuous barriers for the plateau bootstrap.
There are branches for block diameters, inactive caps, the proper active-parent
cap, and the active representative deficit. Vacuous branches equal one. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Metastability.PlateauRegion
open Source CapEnlargement ActiveSourceLaw
variable {n N d : ℕ}

abbrev Index (n : ℕ) :=
  (Block n × Fin n × Fin n) ⊕ ((Block n × Fin n) ⊕ (Fin n ⊕ Unit))

def barrier (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (β κ M : ℝ) (l : Fin N) (i j : Fin n) (x : Configuration n d) : Index n → ℝ := by
  classical
  exact Sum.elim
    (fun p => if p.1 ∈ T.partition l.castSucc ∧ p.2.1 ∈ p.1 ∧ p.2.2 ∈ p.1 then
      Real.exp (-κ * β) - angularDist (x p.2.1) (x p.2.2) else 1)
    (Sum.elim
      (fun p => if hD : p.1 ∈ T.partition l.castSucc then
        if p.1 ≠ T.left l ∧ p.1 ≠ T.right l ∧ p.2 ∈ p.1 then
          (C (T.currentNode l p.1 hD)).radius + M * enlargementScale β -
            angularDist (x p.2) (C (T.currentNode l p.1 hD)).center else 1
        else 1)
      (Sum.elim
        (fun p => if hp : T.parent l ≠ Finset.univ then
          if p ∈ T.parent l then
            (C (T.parentNode l hp)).radius + M * enlargementScale β -
              angularDist (x p) (C (T.parentNode l hp)).center else 1
          else 1)
        (fun _ => upperBarrier C l + 2 * treeMargin hN C -
          (1 - ⟪(x i).val, (x j).val⟫))))

theorem nonneg_iff (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (β κ M : ℝ) (l : Fin N) (i j : Fin n) (x : Configuration n d) :
    (∀ p, 0 ≤ barrier T hN C β κ M l i j x p) ↔
      StageHyp T C β κ M l x ∧
        1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C := by
  classical
  constructor
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro D hD p hp q hq
      simpa [barrier, hD, hp, hq, sub_nonneg] using h (Sum.inl (D, p, q))
    · intro D hD hDl hDr p hp
      simpa [barrier, hD, hDl, hDr, hp, sub_nonneg] using h (Sum.inr (Sum.inl (D, p)))
    · intro hp p hpa
      simpa [barrier, hp, hpa, sub_nonneg] using h (Sum.inr (Sum.inr (Sum.inl p)))
    · simpa [barrier, sub_nonneg] using h (Sum.inr (Sum.inr (Sum.inr ())))
  · rintro ⟨⟨hd, hc, hp⟩, hu⟩ (p | (p | (p | p)))
    · dsimp [barrier]
      split_ifs with h
      · exact sub_nonneg.mpr (hd _ h.1 _ h.2.1 _ h.2.2)
      · norm_num
    · dsimp [barrier]
      split_ifs with hD h
      · exact sub_nonneg.mpr (hc _ hD h.1 h.2.1 _ h.2.2)
      all_goals norm_num
    · by_cases hP : T.parent l ≠ Finset.univ
      · by_cases h : p ∈ T.parent l
        · simpa [barrier, hP, h, sub_nonneg] using hp hP p h
        · simp [barrier, hP, h]
      · simp [barrier, hP]
    · exact sub_nonneg.mpr hu

theorem positive (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (β κ M : ℝ) (l : Fin N) (i j : Fin n) (x : Configuration n d)
    (hd : ∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (x p) (x q) < Real.exp (-κ * β))
    (hc : ∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
      D ≠ T.left l → D ≠ T.right l → ∀ p ∈ D,
      angularDist (x p) (C (T.currentNode l D hD)).center <
        (C (T.currentNode l D hD)).radius + M * enlargementScale β)
    (hp : ∀ hp : T.parent l ≠ Finset.univ, ∀ p ∈ T.parent l,
      angularDist (x p) (C (T.parentNode l hp)).center <
        (C (T.parentNode l hp)).radius + M * enlargementScale β)
    (hu : 1 - ⟪(x i).val, (x j).val⟫ < upperBarrier C l + 2 * treeMargin hN C) :
    ∀ p, 0 < barrier T hN C β κ M l i j x p := by
  classical
  rintro (p | (p | (p | p)))
  · dsimp [barrier]
    split_ifs with h
    · exact sub_pos.mpr (hd _ h.1 _ h.2.1 _ h.2.2)
    · norm_num
  · dsimp [barrier]
    split_ifs with hD h
    · exact sub_pos.mpr (hc _ hD h.1 h.2.1 _ h.2.2)
    all_goals norm_num
  · by_cases hP : T.parent l ≠ Finset.univ
    · by_cases h : p ∈ T.parent l
      · simpa [barrier, hP, h, sub_pos] using hp hP p h
      · simp [barrier, hP, h]
    · simp [barrier, hP]
  · exact sub_pos.mpr hu

theorem continuousOn (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (β κ M : ℝ) (l : Fin N) (i j : Fin n) (x : ℝ → Configuration n d)
    (S : Set ℝ) (hx : ∀ p, ContinuousOn (fun t => (x t p).val) S) :
    ∀ p, ContinuousOn (fun t => barrier T hN C β κ M l i j (x t) p) S := by
  classical
  have hangle : ∀ p q, ContinuousOn (fun t => angularDist (x t p) (x t q)) S := by
    intro p q
    exact Real.continuous_arccos.comp_continuousOn ((hx p).inner (hx q))
  have hcap : ∀ p (w : Sphere d), ContinuousOn (fun t => angularDist (x t p) w) S := by
    intro p w
    exact Real.continuous_arccos.comp_continuousOn ((hx p).inner continuousOn_const)
  rintro (p | (p | (p | p)))
  · dsimp [barrier]
    split_ifs <;> fun_prop (disch := assumption)
  · dsimp [barrier]
    split_ifs <;> fun_prop (disch := assumption)
  · dsimp [barrier]
    split_ifs <;> fun_prop (disch := assumption)
  · exact continuousOn_const.sub (continuousOn_const.sub ((hx i).inner (hx j)))

theorem accelerated_continuous (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hclock : ClockRelation β X shift clock) :
    ∀ p, ContinuousOn (fun t => (accelerated X shift clock t p).val) (Ici 0) := by
  intro p
  have hx : ContinuousOn (fun t => (X t p).val) (Ici 0) :=
    fun t ht => (hX t ht p).continuousWithinAt
  exact hx.comp (continuousOn_const.add
    (ActiveTrajectory.clock_lipschitz model β hβ X hX shift hshift clock hclock).continuousOn)
    (fun t ht => add_nonneg hshift (hclock.1.2.1 t ht))

/-- Geometry-only continuation helper. The dynamical producer must discharge
the strict-improvement premise; it is not an assumption of plateau stability. -/
theorem persist_of_strict_improvement
    (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (β κ M : ℝ) (l : Fin N) (i j : Fin n) (x : ℝ → Configuration n d)
    (a b : ℝ) (hab : a ≤ b)
    (hx : ∀ p, ContinuousOn (fun t => (x t p).val) (Icc a b))
    (hentry : StageHyp T C β κ M l (x a) ∧
      1 - ⟪(x a i).val, (x a j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C)
    (himprove : ∀ e ∈ Icc a b,
      (∀ t ∈ Icc a e, StageHyp T C β κ M l (x t) ∧
        1 - ⟪(x t i).val, (x t j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C) →
      ∀ p, 0 < barrier T hN C β κ M l i j (x e) p) :
    ∀ t ∈ Icc a b, StageHyp T C β κ M l (x t) ∧
      1 - ⟪(x t i).val, (x t j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C := by
  classical
  have hpersist := PlateauBootstrap.persist (Finset.univ : Finset (Index n))
    ⟨Sum.inr (Sum.inr (Sum.inr ())), Finset.mem_univ _⟩
    (fun p t => barrier T hN C β κ M l i j (x t) p) (fun _ => 0) hab
    (fun p _ => continuousOn T hN C β κ M l i j x (Icc a b) hx p)
    (fun p _ => (nonneg_iff T hN C β κ M l i j (x a)).mpr hentry p)
    (by
      intro e he hclosed p _
      apply himprove e he _ p
      intro t ht
      exact (nonneg_iff T hN C β κ M l i j (x t)).mp
        (fun q => hclosed t ht q (Finset.mem_univ _)))
  intro t ht
  exact (nonneg_iff T hN C β κ M l i j (x t)).mp
    (fun p => hpersist t ht p (Finset.mem_univ _))

end Metastability.PlateauRegion
