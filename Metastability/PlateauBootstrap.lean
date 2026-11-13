import Metastability.CapNoExit
import Mathlib.Topology.Order.DenselyOrdered

/-! Finite continuous bootstrap: strict improvement on every closed stopped
interval prevents any of the finitely many geometric barriers from failing. -/

noncomputable section
open Set

namespace Metastability.PlateauBootstrap

/-- Continuity includes the truncated first exit in all closed barriers.
Initial non-strict inequalities also cover an exit equal to the initial time. -/
theorem closed_before_exit {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (R : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (ha : ∀ i ∈ s, R i ≤ f i a) :
    ∀ t ∈ Icc a (CapNoExit.finiteExit s f R a b), ∀ i ∈ s, R i ≤ f i t := by
  let e := CapNoExit.finiteExit s f R a b
  have he : e ∈ Icc a b := CapNoExit.finiteExit_bounds s f R hab
  intro t ht i hi
  by_cases hae : a = e
  · have ht' : t = a := by change t ∈ Icc a e at ht; exact le_antisymm (ht.2.trans hae.symm.le) ht.1
    exact ht' ▸ ha i hi
  · have hclosure : closure (Ico a e) = Icc a e := closure_Ico hae
    apply le_on_closure (s := Ico a e)
      (fun u hu => CapNoExit.le_of_before_finiteExit s f R hab hu i hi)
      continuousOn_const
    · rw [hclosure]
      exact (hc i hi).mono (Icc_subset_Icc_right he.2)
    · rwa [hclosure]

/-- A finite family of continuous closed inequalities persists if it is
initially satisfied and every closed stopped interval improves its endpoint
to strict inequalities. The improvement is a helper premise, discharged by
the dynamical estimates in the source-facing plateau theorem. -/
theorem persist {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ → ℝ) (R : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (ha : ∀ i ∈ s, R i ≤ f i a)
    (himprove : ∀ e ∈ Icc a b,
      (∀ t ∈ Icc a e, ∀ i ∈ s, R i ≤ f i t) → ∀ i ∈ s, R i < f i e) :
    ∀ t ∈ Icc a b, ∀ i ∈ s, R i ≤ f i t := by
  have he := CapNoExit.finiteExit_bounds s f R hab
  have hclosed := closed_before_exit s f R hab hc ha
  have heq := CapNoExit.finiteExit_eq_end_of_strict s hs f R hab hc
    (himprove _ he hclosed)
  simpa only [heq] using hclosed

end Metastability.PlateauBootstrap
