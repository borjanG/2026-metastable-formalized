import Metastability.FiniteMinimum
import Mathlib.Topology.Order.Compact

/-!
# Preserving a positive finite minimum

The derivative condition is imposed only when every branch is nonnegative.
A first-exit argument proves that this region cannot be left from strictly
positive initial data, and then finite-minimum comparison preserves the full
initial lower bound. Positivity on the time interval is a conclusion.
-/

noncomputable section
open Set

namespace Metastability.MinimumBarrier

/-- A positive common lower bound is preserved if every minimizing branch has
nonnegative right derivative whenever all branches are nonnegative. -/
theorem all_ge_of_active_nonneg {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f f' : ι → ℝ → ℝ) {a b m : ℝ} (hm : 0 < m)
    (ha : ∀ i ∈ s, m ≤ f i a)
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∀ i ∈ s,
      HasDerivWithinAt (f i) (f' i x) (Ici x) x)
    (hb : ∀ x ∈ Ico a b, (∀ j ∈ s, 0 ≤ f j x) →
      ∀ i ∈ s, (∀ j ∈ s, f i x ≤ f j x) → 0 ≤ f' i x)
    {t : ℝ} (ht : t ∈ Icc a b) : ∀ i ∈ s, m ≤ f i t := by
  let μ : ℝ → ℝ := fun u => s.inf' hs (fun i => f i u)
  have hstart : m ≤ μ a := Finset.le_inf' hs _ ha
  have hμ : ContinuousOn μ (Icc a b) := ContinuousOn.finset_inf'_apply hs hc
  have hpositive : ∀ x ∈ Icc a b, 0 < μ x := by
    intro x hx
    by_contra hnegative
    let Z : Set ℝ := Icc a b ∩ μ ⁻¹' Iic 0
    have hZclosed : IsClosed Z :=
      hμ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hZcompact : IsCompact Z :=
      isCompact_Icc.of_isClosed_subset hZclosed inter_subset_left
    have hZne : Z.Nonempty := ⟨x, hx, le_of_not_gt hnegative⟩
    obtain ⟨U, hU⟩ := hZcompact.exists_isLeast hZne
    have hUa : a ≤ U := hU.1.1.1
    have hUb : U ≤ b := hU.1.1.2
    have hUneg : μ U ≤ 0 := hU.1.2
    have hbefore : ∀ u ∈ Ico a U, ∀ j ∈ s, 0 ≤ f j u := by
      intro u hu j hj
      have hμu : 0 < μ u := by
        by_contra hnu
        have huZ : u ∈ Z := ⟨⟨hu.1, hu.2.le.trans hUb⟩, le_of_not_gt hnu⟩
        exact (not_le.mpr hu.2) (hU.2 huZ)
      exact hμu.le.trans (Finset.inf'_le (fun k => f k u) hj)
    have hcomp := FiniteMinimum.minimum_lower_bound s hs f f' (C := 0)
      (fun i hi => (hc i hi).mono (Icc_subset_Icc_right hUb))
      (fun u hu => hd u ⟨hu.1, hu.2.trans_le hUb⟩)
      (fun u hu i hi hmin => by
        simpa only [neg_zero] using
          hb u ⟨hu.1, hu.2.trans_le hUb⟩ (hbefore u hu) i hi hmin)
      (show U ∈ Icc a U from ⟨hUa, le_rfl⟩)
    change μ a - 0 * (U - a) ≤ μ U at hcomp
    linarith only [hcomp, hstart, hUneg, hm]
  have hnonneg : ∀ u ∈ Ico a b, ∀ j ∈ s, 0 ≤ f j u := by
    intro u hu j hj
    exact (hpositive u (Ico_subset_Icc_self hu)).le.trans
      (Finset.inf'_le (fun k => f k u) hj)
  have hcomp := FiniteMinimum.minimum_lower_bound s hs f f' (C := 0) hc hd
    (fun u hu i hi hmin => by
      simpa only [neg_zero] using hb u hu (hnonneg u hu) i hi hmin) ht
  change μ a - 0 * (t - a) ≤ μ t at hcomp
  intro i hi
  have hmin : μ t ≤ f i t := Finset.inf'_le (fun j => f j t) hi
  linarith only [hstart, hcomp, hmin]

end Metastability.MinimumBarrier
