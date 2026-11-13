import Metastability.SourceDefinitions

/-!
# Explicit finite empirical couplings

These are the particle-to-center coupling estimates used at the end of the
manuscript. The infimum is over all nonnegative matrices with the prescribed
marginals, exactly as in `Source.empiricalWasserstein`. These estimates do not
assert the unproved dynamical convergence of the particle positions.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace Metastability.FiniteTransport

variable {n d : ℕ}

/-- Matrices with the two uniform empirical marginals. -/
def IsCoupling (γ : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ γ i j) ∧ (∀ i, ∑ j, γ i j = 1 / (n : ℝ)) ∧
    (∀ j, ∑ i, γ i j = 1 / (n : ℝ))

/-- Angular transport cost of a labelled coupling. -/
def cost (x y : Source.Configuration n d) (γ : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, γ i j * Source.angularDist (x i) (y j)

def costs (x y : Source.Configuration n d) : Set ℝ :=
  {c | ∃ γ : Fin n → Fin n → ℝ, IsCoupling γ ∧ c = cost x y γ}

theorem empiricalWasserstein_eq (hn : 0 < n) (x y : Source.Configuration n d) :
    Source.empiricalWasserstein hn x y = sInf (costs x y) := by
  unfold Source.empiricalWasserstein
  congr 1
  ext c
  simp only [costs, IsCoupling, cost, mem_setOf_eq]
  constructor
  · rintro ⟨γ, hpos, hrow, hcol, heq⟩
    exact ⟨γ, ⟨hpos, hrow, hcol⟩, heq⟩
  · rintro ⟨γ, ⟨hpos, hrow, hcol⟩, heq⟩
    exact ⟨γ, hpos, hrow, hcol, heq⟩

def diagonal : Fin n → Fin n → ℝ := fun i j => if i = j then 1 / (n : ℝ) else 0

theorem diagonal_isCoupling : IsCoupling (diagonal (n := n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold diagonal
    split_ifs <;> positivity
  · intro i
    simp only [diagonal, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · intro j
    simp only [diagonal, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem cost_diagonal (x y : Source.Configuration n d) :
    cost x y diagonal = (∑ i, Source.angularDist (x i) (y i)) / n := by
  unfold cost diagonal
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.mul_sum]
  ring

theorem costs_nonempty (x y : Source.Configuration n d) : (costs x y).Nonempty :=
  ⟨cost x y diagonal, diagonal, diagonal_isCoupling, rfl⟩

theorem cost_nonneg (x y : Source.Configuration n d) {γ : Fin n → Fin n → ℝ}
    (hγ : IsCoupling γ) : 0 ≤ cost x y γ := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hγ.1 i j) (Real.arccos_nonneg _)

theorem costs_bddBelow (x y : Source.Configuration n d) : BddBelow (costs x y) := by
  refine ⟨0, ?_⟩
  rintro c ⟨γ, hγ, rfl⟩
  exact cost_nonneg x y hγ

theorem empiricalWasserstein_nonneg (hn : 0 < n) (x y : Source.Configuration n d) :
    0 ≤ Source.empiricalWasserstein hn x y := by
  rw [empiricalWasserstein_eq]
  apply le_csInf (costs_nonempty x y)
  rintro c ⟨γ, hγ, rfl⟩
  exact cost_nonneg x y hγ

/-- Every explicit coupling gives an upper bound on the full infimum. -/
theorem empiricalWasserstein_le_cost (hn : 0 < n) (x y : Source.Configuration n d)
    {γ : Fin n → Fin n → ℝ} (hγ : IsCoupling γ) :
    Source.empiricalWasserstein hn x y ≤ cost x y γ := by
  rw [empiricalWasserstein_eq]
  exact csInf_le (costs_bddBelow x y) ⟨γ, hγ, rfl⟩

/-- Coupling each label to its target center is admissible, including repeated centers. -/
theorem empiricalWasserstein_le_average (hn : 0 < n) (x y : Source.Configuration n d) :
    Source.empiricalWasserstein hn x y ≤ (∑ i, Source.angularDist (x i) (y i)) / n := by
  rw [← cost_diagonal]
  exact empiricalWasserstein_le_cost hn x y diagonal_isCoupling

theorem empiricalWasserstein_le_of_pointwise (hn : 0 < n)
    (x y : Source.Configuration n d) (ε : ℝ)
    (hε : ∀ i, Source.angularDist (x i) (y i) ≤ ε) :
    Source.empiricalWasserstein hn x y ≤ ε := by
  apply (empiricalWasserstein_le_average hn x y).trans
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hn').mpr
  calc
    ∑ i, Source.angularDist (x i) (y i) ≤ ∑ _ : Fin n, ε :=
      Finset.sum_le_sum (fun i _ => hε i)
    _ = ε * n := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The finite particle-to-center estimate passes uniform convergence to the
literal empirical transport cost. This is a general analytic helper. -/
theorem tendstoUniformlyOn_empiricalWasserstein {ι : Type*} {l : Filter ι}
    (hn : 0 < n) (x y : ι → ℝ → Source.Configuration n d) (K : Set ℝ)
    (h : ∀ ε > 0, ∀ᶠ b in l, ∀ t ∈ K, ∀ i,
      Source.angularDist (x b t i) (y b t i) < ε) :
    TendstoUniformlyOn (fun b t => Source.empiricalWasserstein hn (x b t) (y b t))
      (fun _ => 0) l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [h (ε / 2) (by linarith)] with b hb
  intro t ht
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (empiricalWasserstein_nonneg hn _ _)]
  exact (empiricalWasserstein_le_of_pointwise hn _ _ (ε / 2)
    (fun i => (hb t ht i).le)).trans_lt (by linarith)

end Metastability.FiniteTransport
