import Metastability.ModelBounds
import Metastability.AngularGeometry
import Metastability.FiniteMinimum

/-!
# Integrating the cap-coordinate estimate

This is the interval estimate used before a cap exit. Its geometric positivity
and exterior-barrier premises describe that stopped interval explicitly. The
finite minimum may switch minimizing labels; the proof uses right slopes and
does not assume classical differentiability of that minimum.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Metastability.CapDrift
variable {n d : ℕ} {model : Source.Model} {β : ℝ}

/-- Differentiation of a fixed cap coordinate from the literal source ODE. -/
theorem coordinate_hasDerivWithinAt (X : ℝ → Source.Configuration n d)
    (hX : Source.Solves model β X) (w : Source.Sphere d) (i : Fin n)
    (u : ℝ) (hu : 0 ≤ u) :
    HasDerivWithinAt (fun v => ⟪(X v i).val, w.val⟫)
      ⟪Source.vectorField model β (X u) i, w.val⟫ (Ici u) u := by
  have hd := (hX u hu i).mono (Ici_subset_Ici.mpr hu)
  simpa only [inner_zero_right, add_zero, zero_add] using
    hd.inner ℝ (hasDerivWithinAt_const u (Ici u) w.val)

theorem coordinate_continuousOn (X : ℝ → Source.Configuration n d)
    (hX : Source.Solves model β X) (w : Source.Sphere d) (i : Fin n)
    (a b : ℝ) (ha : 0 ≤ a) :
    ContinuousOn (fun u => ⟪(X u i).val, w.val⟫) (Icc a b) := by
  have hc : ContinuousOn (fun u => (X u i).val) (Ici 0) :=
    fun u hu => (hX u hu i).continuousWithinAt
  exact (hc.inner continuousOn_const).mono (fun u hu => ha.trans hu.1)

/-- The source one-sided cap estimate on an interval where the block's cap
coordinates stay nonnegative and all exterior interaction barriers exceed L.
The bound has the explicit constant 2n, common to SA and USA. -/
theorem cap_drift_on_interval (X : ℝ → Source.Configuration n d)
    (hX : Source.Solves model β X) (hβ : 0 ≤ β)
    (A : Source.Block n) (hA : A.Nonempty) (w : Source.Sphere d)
    (a b r L : ℝ) (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hrπ : r ≤ Real.pi)
    (hinitial : ∀ i ∈ A, Source.angularDist (X a i) w ≤ r)
    (hpositive : ∀ u ∈ Ico a b, ∀ i ∈ A, 0 ≤ ⟪(X u i).val, w.val⟫)
    (hsep : ∀ u ∈ Ico a b, ∀ i ∈ A, ∀ j ∉ A,
      ⟪(X u i).val, (X u j).val⟫ ≤ 1 - L)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ∀ i ∈ A, Real.cos r - (2 * n) * (t - a) * Real.exp (-β * L) ≤
      ⟪(X t i).val, w.val⟫ := by
  let f : Fin n → ℝ → ℝ := fun i u => ⟪(X u i).val, w.val⟫
  let f' : Fin n → ℝ → ℝ := fun i u => ⟪Source.vectorField model β (X u) i, w.val⟫
  let C : ℝ := (2 * n) * Real.exp (-β * L)
  have hcont : ∀ i ∈ A, ContinuousOn (f i) (Icc a b) :=
    fun i _ => coordinate_continuousOn X hX w i a b ha
  have hd : ∀ u ∈ Ico a b, ∀ i ∈ A, HasDerivWithinAt (f i) (f' i u) (Ici u) u :=
    fun u hu i _ => coordinate_hasDerivWithinAt X hX w i u (ha.trans hu.1)
  have hb : ∀ u ∈ Ico a b, ∀ i ∈ A, (∀ j ∈ A, f i u ≤ f j u) → -C ≤ f' i u := by
    intro u hu i hi hmin
    have hh := ModelBounds.cap_minimum_vectorField_lower model β L hβ (X u) A i w
      (hpositive u hu i hi) hmin (hsep u hu i hi)
    dsimp [C, f']
    linarith
  have hstart : Real.cos r ≤ A.inf' hA (fun i => f i a) := by
    apply Finset.le_inf'
    intro i hi
    exact (AngularGeometry.angularDist_le_iff_inner _ _ hr0 hrπ).mp (hinitial i hi)
  have hmin := FiniteMinimum.minimum_lower_bound A hA f f' hcont hd hb ht
  intro i hi
  have hi' : A.inf' hA (fun j => f j t) ≤ f i t := Finset.inf'_le _ hi
  dsimp [f, C] at hstart hmin hi'
  nlinarith

end Metastability.CapDrift
