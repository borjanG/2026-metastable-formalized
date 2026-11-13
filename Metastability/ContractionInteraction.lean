import Metastability.KernelComparison
import Mathlib.Topology.Order.Lattice

/-!
# The literal exterior interaction in the block-contraction lemma

The source density keeps its angular sine-squared factor and exponential
barrier. The supremum over a nonempty finite block is its genuine maximum.
Continuity and the uniform separated-block bound are proved below.
-/

noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace Metastability.ContractionInteraction

open Source
variable {n d : ℕ}

def interaction (β : ℝ) (u v : Sphere d) : ℝ :=
  (1 + β * Real.sin (angularDist u v) ^ 2) *
    Real.exp (-β * (1 - Real.cos (angularDist u v)))

def exterior (β : ℝ) (x : Configuration n d) (D : Block n) (hD : D.Nonempty) : ℝ :=
  ∑ k ∈ Finset.univ \ D, D.sup' hD (fun a => interaction β (x a) (x k))

theorem interaction_eq_inner (β : ℝ) (u v : Sphere d) :
    interaction β u v = (1 + β * (1 - ⟪u.val, v.val⟫ ^ 2)) *
      Real.exp (β * (⟪u.val, v.val⟫ - 1)) := by
  have hs : Real.sin (angularDist u v) ^ 2 = 1 - ⟪u.val, v.val⟫ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (angularDist u v)
    rw [AngularGeometry.cos_angularDist] at h
    linarith only [h]
  unfold interaction
  rw [hs, AngularGeometry.cos_angularDist]
  congr 2
  ring

theorem interaction_nonneg (β : ℝ) (hβ : 0 ≤ β) (u v : Sphere d) :
    0 ≤ interaction β u v := by
  unfold interaction
  positivity

theorem interaction_le_sup (β : ℝ) (x : Configuration n d)
    (D : Block n) (hD : D.Nonempty) {i : Fin n} (hi : i ∈ D) (k : Fin n) :
    interaction β (x i) (x k) ≤ D.sup' hD (fun a => interaction β (x a) (x k)) :=
  Finset.le_sup' (fun a => interaction β (x a) (x k)) hi

theorem max_interaction_le_sup (β : ℝ) (x : Configuration n d)
    (D : Block n) (hD : D.Nonempty) {i j : Fin n} (hi : i ∈ D) (hj : j ∈ D)
    (k : Fin n) :
    max (interaction β (x i) (x k)) (interaction β (x j) (x k)) ≤
      D.sup' hD (fun a => interaction β (x a) (x k)) :=
  max_le (interaction_le_sup β x D hD hi k) (interaction_le_sup β x D hD hj k)

theorem sup_interaction_nonneg (β : ℝ) (hβ : 0 ≤ β) (x : Configuration n d)
    (D : Block n) (hD : D.Nonempty) (k : Fin n) :
    0 ≤ D.sup' hD (fun a => interaction β (x a) (x k)) := by
  obtain ⟨i, hi⟩ := hD
  exact (interaction_nonneg β hβ (x i) (x k)).trans
    (Finset.le_sup' (fun a => interaction β (x a) (x k)) hi)

theorem exterior_nonneg (β : ℝ) (hβ : 0 ≤ β) (x : Configuration n d)
    (D : Block n) (hD : D.Nonempty) : 0 ≤ exterior β x D hD :=
  Finset.sum_nonneg (fun k _ => sup_interaction_nonneg β hβ x D hD k)

/-- An exterior endpoint contributes at most the uniform separated density. -/
theorem interaction_le_of_barrier (β b : ℝ) (hβ : 0 ≤ β) (u v : Sphere d)
    (hsep : b ≤ 1 - ⟪u.val, v.val⟫) :
    interaction β u v ≤ (1 + β) * Real.exp (-β * b) := by
  have hfactor : 1 + β * Real.sin (angularDist u v) ^ 2 ≤ 1 + β := by
    have h := mul_le_mul_of_nonneg_left (Real.sin_sq_le_one (angularDist u v)) hβ
    linarith only [h]
  have he : Real.exp (-β * (1 - Real.cos (angularDist u v))) ≤
      Real.exp (-β * b) := by
    rw [AngularGeometry.cos_angularDist]
    apply Real.exp_le_exp.mpr
    nlinarith only [hsep, hβ]
  exact mul_le_mul hfactor he (Real.exp_pos _).le (by linarith only [hβ])

/-- The source exterior interaction is exponentially small under a uniform
particlewise barrier. The factor n is the original source particle count. -/
theorem exterior_le_of_barrier (β b : ℝ) (hβ : 0 ≤ β) (x : Configuration n d)
    (D : Block n) (hD : D.Nonempty)
    (hsep : ∀ i ∈ D, ∀ k ∉ D, b ≤ 1 - ⟪(x i).val, (x k).val⟫) :
    exterior β x D hD ≤ n * (1 + β) * Real.exp (-β * b) := by
  have hterm : ∀ k ∈ Finset.univ \ D,
      D.sup' hD (fun a => interaction β (x a) (x k)) ≤ (1 + β) * Real.exp (-β * b) := by
    intro k hk
    apply Finset.sup'_le hD
    intro i hi
    exact interaction_le_of_barrier β b hβ (x i) (x k)
      (hsep i hi k (Finset.mem_sdiff.mp hk).2)
  have hc : ((Finset.univ \ D).card : ℝ) ≤ n := by
    exact_mod_cast (show (Finset.univ \ D).card ≤ n by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ (Finset.univ \ D)))
  have hm : 0 ≤ (1 + β) * Real.exp (-β * b) := by positivity
  calc
    exterior β x D hD ≤ ∑ _k ∈ Finset.univ \ D, (1 + β) * Real.exp (-β * b) :=
      Finset.sum_le_sum hterm
    _ = ((Finset.univ \ D).card : ℝ) * ((1 + β) * Real.exp (-β * b)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * ((1 + β) * Real.exp (-β * b)) := mul_le_mul_of_nonneg_right hc hm
    _ = n * (1 + β) * Real.exp (-β * b) := by ring

theorem continuousOn_interaction {α : Type*} [TopologicalSpace α]
    (β : ℝ) (u v : α → Sphere d) (S : Set α)
    (hu : ContinuousOn (fun t => (u t).val) S)
    (hv : ContinuousOn (fun t => (v t).val) S) :
    ContinuousOn (fun t => interaction β (u t) (v t)) S := by
  simp_rw [interaction_eq_inner]
  have hi : ContinuousOn (fun t => ⟪(u t).val, (v t).val⟫) S := hu.inner hv
  exact (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub (hi.pow 2)))).mul
    (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (hi.sub continuousOn_const)))

theorem continuousOn_exterior {α : Type*} [TopologicalSpace α]
    (β : ℝ) (X : α → Configuration n d) (D : Block n) (hD : D.Nonempty) (S : Set α)
    (hX : ∀ i, ContinuousOn (fun t => (X t i).val) S) :
    ContinuousOn (fun t => exterior β (X t) D hD) S := by
  unfold exterior
  apply continuousOn_finset_sum
  intro k _
  apply ContinuousOn.finset_sup'_apply hD
  intro i _
  exact continuousOn_interaction β (fun t => X t i) (fun t => X t k) S (hX i) (hX k)

/-- Continuity on the original half-line follows from the source ODE alone. -/
theorem continuousOn_exterior_of_solves (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (D : Block n) (hD : D.Nonempty) :
    ContinuousOn (fun t => exterior β (X t) D hD) (Ici 0) := by
  apply continuousOn_exterior β X D hD (Ici 0)
  intro i t ht
  exact (hX t ht i).continuousWithinAt

end Metastability.ContractionInteraction
