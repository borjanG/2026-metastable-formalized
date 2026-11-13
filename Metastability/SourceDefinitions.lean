import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Finset.Max
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Literal objects from the metastability manuscript

This module supplies mathematical definitions, not a proof of the cascade.
`angularDist` is deliberately separate from the inherited ambient metric.
The source is the pinned `source/main.tex`; these declarations await independent
source review and author approval and are not frozen declarations.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace
open Filter Set

namespace Metastability.Source

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Sphere (d : ℕ) := { x : Vector d // ‖x‖ = 1 }
abbrev Configuration (n d : ℕ) := Fin n → Sphere d
abbrev Block (n : ℕ) := Finset (Fin n)

/-- The paper's distance is angular, rather than the subtype's ambient distance. -/
def angularDist {d : ℕ} (x y : Sphere d) : ℝ :=
  Real.arccos ⟪x.val, y.val⟫

/-- A proper-node cap has radius strictly below a hemisphere. -/
structure SphericalCap (d : ℕ) where
  center : Sphere d
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  radius_lt_half_pi : radius < Real.pi / 2

def SphericalCap.carrier {d : ℕ} (C : SphericalCap d) : Set (Sphere d) :=
  {x | angularDist x C.center ≤ C.radius}

def capMinDistance {d : ℕ} (C D : SphericalCap d) : ℝ :=
  sInf {r | ∃ x ∈ C.carrier, ∃ y ∈ D.carrier, r = angularDist x y}

def capMaxDistance {d : ℕ} (C D : SphericalCap d) : ℝ :=
  sSup {r | ∃ x ∈ C.carrier, ∃ y ∈ D.carrier, r = angularDist x y}

/-- The ordered full binary collision tree, encoded exactly by its partitions. -/
structure CollisionTree (n N : ℕ) where
  partition : Fin (N + 1) → Finset (Block n)
  left : Fin N → Block n
  right : Fin N → Block n
  block_nonempty : ∀ l D, D ∈ partition l → D.Nonempty
  block_disjoint : ∀ l D E, D ∈ partition l → E ∈ partition l → D ≠ E → Disjoint D E
  partition_cover : ∀ l, (partition l).biUnion id = Finset.univ
  left_mem : ∀ l, left l ∈ partition l.castSucc
  right_mem : ∀ l, right l ∈ partition l.castSucc
  children_ne : ∀ l, left l ≠ right l
  merge : ∀ l, partition l.succ =
    insert (left l ∪ right l) (((partition l.castSucc).erase (left l)).erase (right l))
  final_partition : partition (Fin.last N) = {Finset.univ}

namespace CollisionTree

variable {n N : ℕ} (T : CollisionTree n N)

def parent (l : Fin N) : Block n := T.left l ∪ T.right l

def IsNode (D : Block n) : Prop := ∃ l, D ∈ T.partition l

abbrev ProperNode := {D : Block n // T.IsNode D ∧ D ≠ Finset.univ}

theorem left_node (l : Fin N) : T.IsNode (T.left l) := ⟨l.castSucc, T.left_mem l⟩
theorem right_node (l : Fin N) : T.IsNode (T.right l) := ⟨l.castSucc, T.right_mem l⟩

theorem parent_node (l : Fin N) : T.IsNode (T.parent l) := by
  refine ⟨l.succ, ?_⟩
  rw [T.merge l]
  exact Finset.mem_insert_self _ _

include T in
theorem particle_pos (hN : 0 < N) : 0 < n := by
  obtain ⟨i, _⟩ := T.block_nonempty _ _ (T.left_mem ⟨0, hN⟩)
  exact Nat.zero_lt_of_lt i.isLt

theorem left_proper (l : Fin N) : T.left l ≠ Finset.univ := by
  intro h
  obtain ⟨i, hi⟩ := T.block_nonempty _ _ (T.right_mem l)
  have hd := T.block_disjoint _ _ _ (T.left_mem l) (T.right_mem l) (T.children_ne l)
  exact Finset.disjoint_left.mp hd (h ▸ Finset.mem_univ i) hi

theorem right_proper (l : Fin N) : T.right l ≠ Finset.univ := by
  intro h
  obtain ⟨i, hi⟩ := T.block_nonempty _ _ (T.left_mem l)
  have hd := T.block_disjoint _ _ _ (T.left_mem l) (T.right_mem l) (T.children_ne l)
  exact Finset.disjoint_left.mp hd hi (h ▸ Finset.mem_univ i)

theorem current_block_proper (l : Fin N) (D : Block n)
    (hD : D ∈ T.partition l.castSucc) : D ≠ Finset.univ := by
  by_cases hleft : D = T.left l
  · simpa only [hleft] using T.left_proper l
  · intro h
    obtain ⟨i, hi⟩ := T.block_nonempty _ _ (T.left_mem l)
    have hd := T.block_disjoint _ _ _ hD (T.left_mem l) hleft
    exact Finset.disjoint_left.mp hd (h ▸ Finset.mem_univ i) hi

def currentNode (l : Fin N) (D : Block n) (hD : D ∈ T.partition l.castSucc) :
    T.ProperNode :=
  ⟨D, ⟨l.castSucc, hD⟩, T.current_block_proper l D hD⟩

def leftNode (l : Fin N) : T.ProperNode :=
  ⟨T.left l, T.left_node l, T.left_proper l⟩

def rightNode (l : Fin N) : T.ProperNode :=
  ⟨T.right l, T.right_node l, T.right_proper l⟩

def parentNode (l : Fin N) (h : T.parent l ≠ Finset.univ) : T.ProperNode :=
  ⟨T.parent l, T.parent_node l, h⟩

theorem existsUnique_block (l : Fin (N + 1)) (i : Fin n) :
    ∃! D : Block n, D ∈ T.partition l ∧ i ∈ D := by
  have hm : i ∈ (T.partition l).biUnion id := by
    rw [T.partition_cover l]
    exact Finset.mem_univ i
  obtain ⟨D, hD, hi⟩ := Finset.mem_biUnion.mp hm
  refine ⟨D, ⟨hD, hi⟩, ?_⟩
  intro E hE
  by_contra hne
  exact Finset.disjoint_left.mp
    (T.block_disjoint l E D hE.1 hD hne) hE.2 hi

/-- The unique block containing a label; its characterization is proved below. -/
def blockOf (l : Fin (N + 1)) (i : Fin n) : Block n :=
  Classical.choose (T.existsUnique_block l i)

theorem blockOf_spec (l : Fin (N + 1)) (i : Fin n) :
    T.blockOf l i ∈ T.partition l ∧ i ∈ T.blockOf l i :=
  (Classical.choose_spec (T.existsUnique_block l i)).1

theorem blockOf_unique (l : Fin (N + 1)) (i : Fin n) (D : Block n)
    (hD : D ∈ T.partition l) (hi : i ∈ D) : D = T.blockOf l i :=
  (Classical.choose_spec (T.existsUnique_block l i)).2 D ⟨hD, hi⟩

end CollisionTree

/-- Caps are supplied only for proper nodes, with no root cap. -/
abbrev TreeCaps {n N : ℕ} (T : CollisionTree n N) (d : ℕ) :=
  T.ProperNode → SphericalCap d

def lowerAngle {n N d : ℕ} {T : CollisionTree n N} (C : TreeCaps T d) (l : Fin N) : ℝ :=
  capMinDistance (C (T.leftNode l)) (C (T.rightNode l))

def upperAngle {n N d : ℕ} {T : CollisionTree n N} (C : TreeCaps T d) (l : Fin N) : ℝ :=
  capMaxDistance (C (T.leftNode l)) (C (T.rightNode l))

def lowerBarrier {n N d : ℕ} {T : CollisionTree n N} (C : TreeCaps T d) (l : Fin N) : ℝ :=
  1 - Real.cos (lowerAngle C l)

def upperBarrier {n N d : ℕ} {T : CollisionTree n N} (C : TreeCaps T d) (l : Fin N) : ℝ :=
  1 - Real.cos (upperAngle C l)

def previousUpperBarrier {n N d : ℕ} {T : CollisionTree n N}
    (C : TreeCaps T d) (l : Fin N) : ℝ :=
  if h : l.val = 0 then 0 else upperBarrier C ⟨l.val - 1, by omega⟩

def outsideBarrier {n N d : ℕ} {T : CollisionTree n N}
    (C : TreeCaps T d) (l : Fin N) : ℝ :=
  if h : T.parent l = Finset.univ then 2 else
    1 - Real.cos (sInf {r | ∃ D : T.ProperNode,
      D.val ∈ T.partition l.castSucc ∧ D.val ≠ T.left l ∧ D.val ≠ T.right l ∧
      r = capMinDistance (C (T.parentNode l h)) (C D)})

/-- Definition 2.1, with all geometric preparation hypotheses exposed. -/
def StrictlyPrepared {n N d : ℕ} {T : CollisionTree n N} (C : TreeCaps T d) : Prop :=
  (∀ l (h : T.parent l ≠ Finset.univ),
    (C (T.leftNode l)).carrier ∪ (C (T.rightNode l)).carrier ⊆
      (C (T.parentNode l h)).carrier) ∧
  ∀ l, 0 < lowerAngle C l ∧ lowerAngle C l ≤ upperAngle C l ∧
    upperAngle C l < Real.pi ∧ previousUpperBarrier C l < lowerBarrier C l ∧
    lowerBarrier C l ≤ upperBarrier C l ∧ upperBarrier C l < outsideBarrier C l

inductive Model where
  | usa
  | sa
  deriving DecidableEq

def projectTangent {d : ℕ} (x : Sphere d) (v : Vector d) : Vector d :=
  v - ⟪x.val, v⟫ • x.val

def coefficient {n d : ℕ} (model : Model) (β : ℝ) (x : Configuration n d)
    (i j : Fin n) : ℝ :=
  match model with
  | .usa => Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)) / n
  | .sa => Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)) /
      ∑ k, Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1))

def vectorField {n d : ℕ} (model : Model) (β : ℝ) (x : Configuration n d)
    (i : Fin n) : Vector d :=
  projectTangent (x i) (∑ j, coefficient model β x i j • (x j).val)

/-- The source ODE premise, without any dynamical estimate added. -/
def Solves {n d : ℕ} (model : Model) (β : ℝ) (x : ℝ → Configuration n d) : Prop :=
  ∀ t ∈ Ici (0 : ℝ), ∀ i,
    HasDerivWithinAt (fun s => (x s i).val) (vectorField model β (x t) i) (Ici 0) t

def energy {n d : ℕ} (β : ℝ) (x : Configuration n d) : ℝ :=
  (∑ i, ∑ j, Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1))) / (n : ℝ) ^ 2

def visibleScale (β : ℝ) : ℝ := 1 / Real.sqrt (β * Real.log β)
def clockCutoff (β : ℝ) : ℝ := visibleScale β / 4

def eligiblePairs {n d : ℕ} (β : ℝ) (x : Configuration n d) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => p.1 ≠ p.2 ∧ clockCutoff β < angularDist (x p.1) (x p.2)

/-- The exact finite minimum and the source's all-complete fallback. -/
def clockFactor {n d : ℕ} (β : ℝ) (x : Configuration n d) : ℝ :=
  if h : (eligiblePairs β x).Nonempty then
    Real.log β * ((eligiblePairs β x).image fun p =>
      Real.exp (β * (1 - ⟪(x p.1).val, (x p.2).val⟫))).min'
        (Finset.Nonempty.image h _)
  else 1

/-- The visible preparation required for every real inverse temperature above one. -/
def VisiblePrepared {n N d : ℕ} {T : CollisionTree n N} (hN : 0 < N)
    (C : TreeCaps T d) (β : ℝ) (x : Configuration n d) : Prop :=
  ∀ D (hD : D ∈ T.partition (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1))),
    (∀ i ∈ D, ∀ j ∈ D, angularDist (x i) (x j) ≤ visibleScale β) ∧
    ∀ i ∈ D, angularDist (x i) (C (T.currentNode ⟨0, hN⟩ D hD)).center ≤ visibleScale β

def accelerated {n d : ℕ} (x : ℝ → Configuration n d) (shift : ℝ)
    (clock : ℝ → ℝ) (t : ℝ) : Configuration n d :=
  x (shift + clock t)

/-- The inverse-clock integral in the paragraph immediately after the theorem. -/
def originalClockTime {n d : ℕ} (β : ℝ) (x : ℝ → Configuration n d)
    (shift u : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..u, (clockFactor β (x (shift + v)))⁻¹

/-- The source clock equation in the required locally absolutely continuous sense.
Its existence is a theorem obligation, not part of a solution premise. -/
def IsClock {n d : ℕ} (β : ℝ) (x : ℝ → Configuration n d)
    (shift : ℝ) (clock : ℝ → ℝ) : Prop :=
  clock 0 = 0 ∧ (∀ t ∈ Ici (0 : ℝ), 0 ≤ clock t) ∧
  (∀ b ∈ Ici (0 : ℝ), AbsolutelyContinuousOnInterval clock 0 b) ∧
  ∀ᵐ t ∂MeasureTheory.volume.restrict (Ici (0 : ℝ)),
    HasDerivAt clock (clockFactor β (accelerated x shift clock t)) t

/-- The clock is the inverse of the source integral on nonnegative times.
The differential and regularity conditions are kept explicit for statement auditing. -/
def ClockRelation {n d : ℕ} (β : ℝ) (x : ℝ → Configuration n d)
    (shift : ℝ) (clock : ℝ → ℝ) : Prop :=
  IsClock β x shift clock ∧
  StrictMonoOn clock (Ici (0 : ℝ)) ∧
  (∀ u ∈ Ici (0 : ℝ), 0 ≤ originalClockTime β x shift u) ∧
  (∀ t ∈ Ici (0 : ℝ), originalClockTime β x shift (clock t) = t) ∧
  ∀ u ∈ Ici (0 : ℝ), clock (originalClockTime β x shift u) = u

def stageRate {n N : ℕ} (model : Model) (T : CollisionTree n N) (l : Fin N) : ℝ :=
  match model with
  | .usa => ((T.left l).card + (T.right l).card : ℝ) / n
  | .sa => ((T.left l).card : ℝ) / (T.right l).card +
      ((T.right l).card : ℝ) / (T.left l).card

/-- Finite sums encode the source's recursive jump times exactly. -/
def jumpTime {n N : ℕ} (model : Model) (T : CollisionTree n N) (l : Fin (N + 1)) : ℝ :=
  ∑ k : Fin N, if k.val < l.val then 1 / (2 * stageRate model T k) else 0

def plateauEnergy {n N : ℕ} (T : CollisionTree n N) (l : Fin (N + 1)) : ℝ :=
  (∑ D ∈ T.partition l, (D.card : ℝ) ^ 2) / (n : ℝ) ^ 2

def staircase {n N : ℕ} (model : Model) (T : CollisionTree n N) (t : ℝ) : ℝ :=
  (∑ l : Fin N, if jumpTime model T l.castSucc ≤ t ∧ t < jumpTime model T l.succ
    then plateauEnergy T l.castSucc else 0) +
  if jumpTime model T (Fin.last N) ≤ t then 1 else 0

def centerWeight (model : Model) {n : ℕ} (D : Block n) : ℝ :=
  match model with
  | .usa => D.card
  | .sa => (D.card : ℝ) ^ 2

theorem centerWeight_pos (model : Model) {n : ℕ} (D : Block n) (hD : D.Nonempty) :
    0 < centerWeight model D := by
  have hc : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.mpr hD
  cases model <;> simp only [centerWeight]
  · exact hc
  · positivity

/-- Literal spherical interpolation, including its genuine coincident-point case.
The codomain is ambient; no unit-norm theorem is presumed by this definition. -/
def geodesicBarycenter {d : ℕ} (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b)
    (u v : Sphere d) (_h : angularDist u v < Real.pi) : Vector d :=
  if u = v then u.val else
    (Real.sin (a / (a + b) * angularDist u v) / Real.sin (angularDist u v)) • u.val +
    (Real.sin (b / (a + b) * angularDist u v) / Real.sin (angularDist u v)) • v.val

abbrev NodeCenters {n N : ℕ} (T : CollisionTree n N) (d : ℕ) :=
  (D : Block n) → T.IsNode D → Sphere d

/-- The manuscript's recursive defining equations for deterministic centers.
This does not assume existence, uniqueness, or any dynamical convergence. -/
def IsDeterministicCenters {n N d : ℕ} (model : Model) {T : CollisionTree n N}
    (hN : 0 < N) (C : TreeCaps T d) (z : NodeCenters T d) : Prop :=
  (∀ D (hD : D ∈ T.partition (⟨0, Nat.zero_lt_succ N⟩ : Fin (N + 1))),
    z D ⟨_, hD⟩ = (C (T.currentNode ⟨0, hN⟩ D hD)).center) ∧
  ∀ l, ∃ h : angularDist (z (T.left l) (T.left_node l))
      (z (T.right l) (T.right_node l)) < Real.pi,
    (z (T.parent l) (T.parent_node l)).val =
      geodesicBarycenter (centerWeight model (T.left l)) (centerWeight model (T.right l))
        (centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l)))
        (centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l)))
        (z (T.left l) (T.left_node l)) (z (T.right l) (T.right_node l)) h

/-- Repeating a block's center once per particle gives exactly its mass |D|/n. -/
def partitionConfiguration {n N d : ℕ} (T : CollisionTree n N) (z : NodeCenters T d)
    (l : Fin (N + 1)) : Configuration n d :=
  fun i => z (T.blockOf l i) ⟨l, (T.blockOf_spec l i).1⟩

/-- Equal-weight atomic angular transport cost, minimized over every coupling.
Both arguments are configurations of the same nonzero number of particles. -/
def empiricalWasserstein {n d : ℕ} (_hn : 0 < n)
    (x y : Configuration n d) : ℝ :=
  sInf {c | ∃ γ : Fin n → Fin n → ℝ,
    (∀ i j, 0 ≤ γ i j) ∧
    (∀ i, ∑ j, γ i j = 1 / (n : ℝ)) ∧
    (∀ j, ∑ i, γ i j = 1 / (n : ℝ)) ∧
    c = ∑ i, ∑ j, γ i j * angularDist (x i) (y j)}

end Metastability.Source
