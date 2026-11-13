import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Linarith

/-!
# Comparing a finite minimum using only its active derivatives

The finite minimum need not be differentiable when its minimizing index changes.
The right slopes of its negative are nevertheless bounded above whenever every
active branch has the required lower derivative bound. A one-sided comparison
theorem integrates this slope estimate on a closed interval.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace Metastability.FiniteMinimum

variable {ι : Type*}

/-- The upper right slopes of the negative minimum are controlled by the
derivatives of all minimizing branches. Inactive branches stay below the
comparison line locally because they have a strict value gap. -/
theorem eventually_neg_inf'_slope_lt (s : Finset ι) (hs : s.Nonempty)
    (f f' : ι → ℝ → ℝ) (x C r : ℝ)
    (hd : ∀ i ∈ s, HasDerivWithinAt (f i) (f' i x) (Ici x) x)
    (hb : ∀ i ∈ s, (∀ j ∈ s, f i x ≤ f j x) → -C ≤ f' i x)
    (hr : C < r) :
    ∀ᶠ z in 𝓝[>] x,
      slope (fun u => -(s.inf' hs (fun i => f i u))) x z < r := by
  let m : ℝ → ℝ := fun u => s.inf' hs (fun i => f i u)
  have hbranch : ∀ i ∈ s, ∀ᶠ z in 𝓝[>] x, -f i z < -m x + r * (z - x) := by
    intro i hi
    have hmin : m x ≤ f i x := Finset.inf'_le (fun j => f j x) hi
    by_cases hactive : f i x = m x
    · have hderiv : -f' i x < r := by
        have hbound := hb i hi (fun j hj => hactive ▸ Finset.inf'_le (fun k => f k x) hj)
        linarith
      have he := (hd i hi).neg.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hderiv
      filter_upwards [he, self_mem_nhdsWithin] with z hz hxz
      rw [slope_def_field] at hz
      have hz' := (div_lt_iff₀ (sub_pos.mpr hxz)).mp hz
      change -f i z - -f i x < r * (z - x) at hz'
      rw [hactive] at hz'
      linarith
    · have hstrict : m x < f i x := lt_of_le_of_ne hmin (Ne.symm hactive)
      have hc : Continuous (fun z : ℝ => -m x + r * (z - x)) := by fun_prop
      apply ((hd i hi).neg.continuousWithinAt.mono Ioi_subset_Ici_self).eventually_lt
        hc.continuousAt.continuousWithinAt
      simpa only [sub_self, mul_zero, add_zero, Pi.neg_apply, neg_lt_neg_iff] using hstrict
  have hall : ∀ᶠ z in 𝓝[>] x, ∀ i ∈ s, -f i z < -m x + r * (z - x) :=
    (eventually_all_finset s).mpr hbranch
  filter_upwards [hall, self_mem_nhdsWithin] with z hz hxz
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hs (fun i => f i z)
  rw [slope_def_field]
  apply (div_lt_iff₀ (sub_pos.mpr hxz)).mpr
  have hi' := hz i hi
  change -m z - -m x < r * (z - x)
  change m z = f i z at heq
  rw [heq]
  linarith

/-- A finite minimum decreases no faster than `C` if every minimizing branch
has right derivative at least `-C`. No differentiability of the minimum, sign
condition on `C`, or derivative bound on inactive branches is assumed. -/
theorem minimum_lower_bound (s : Finset ι) (hs : s.Nonempty)
    (f f' : ι → ℝ → ℝ) {a b C : ℝ}
    (hc : ∀ i ∈ s, ContinuousOn (f i) (Icc a b))
    (hd : ∀ x ∈ Ico a b, ∀ i ∈ s,
      HasDerivWithinAt (f i) (f' i x) (Ici x) x)
    (hb : ∀ x ∈ Ico a b, ∀ i ∈ s,
      (∀ j ∈ s, f i x ≤ f j x) → -C ≤ f' i x)
    {t : ℝ} (ht : t ∈ Icc a b) :
    s.inf' hs (fun i => f i a) - C * (t - a) ≤ s.inf' hs (fun i => f i t) := by
  let m : ℝ → ℝ := fun u => s.inf' hs (fun i => f i u)
  have hm : ContinuousOn (fun u => -m u) (Icc a b) :=
    (ContinuousOn.finset_inf'_apply hs hc).neg
  have hB : ContinuousOn (fun u => -m a + C * (u - a)) (Icc a b) := by fun_prop
  have hBd : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun u => -m a + C * (u - a)) C (Ici x) x := by
    intro x _
    simpa only [mul_one] using
      (((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul C).const_add (-m a)
  have h := image_le_of_liminf_slope_right_le_deriv_boundary hm
    (B' := fun _ => C) (by simp only [sub_self, mul_zero, add_zero, le_refl]) hB hBd
    (fun x hx r hr => (eventually_neg_inf'_slope_lt s hs f f' x C r
      (hd x hx) (hb x hx) hr).frequently) ht
  change -m t ≤ -m a + C * (t - a) at h
  change m a - C * (t - a) ≤ m t
  linarith

end Metastability.FiniteMinimum
