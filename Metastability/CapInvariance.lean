import Metastability.CapDrift
import Metastability.MinimumBarrier
import Metastability.EnergyEstimates

/-!
# Forward invariance of a full-particle spherical cap

This is the manuscript's terminal confinement argument. It holds for any
number of particles, for either model, and for all later original times.
The proof derives positivity by first exit rather than assuming confinement.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Metastability.CapInvariance
variable {n d : ℕ} {model : Source.Model} {β : ℝ}

/-- A cap strictly smaller than a hemisphere containing every particle is
forward invariant under either source ODE. -/
theorem full_cap_forward_invariant (hn : 0 < n)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (C : Source.SphericalCap d) (a : ℝ) (ha : 0 ≤ a)
    (hinitial : ∀ i, X a i ∈ C.carrier) :
    ∀ t, a ≤ t → ∀ i, X t i ∈ C.carrier := by
  intro t ht
  let f : Fin n → ℝ → ℝ := fun i u => ⟪(X u i).val, C.center.val⟫
  let f' : Fin n → ℝ → ℝ := fun i u =>
    ⟪Source.vectorField model β (X u) i, C.center.val⟫
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hstart : ∀ i ∈ (Finset.univ : Finset (Fin n)), Real.cos C.radius ≤ f i a := by
    intro i _
    exact (AngularGeometry.cap_mem_iff_inner C _).mp (hinitial i)
  have hc : ∀ i ∈ (Finset.univ : Finset (Fin n)), ContinuousOn (f i) (Icc a t) :=
    fun i _ => CapDrift.coordinate_continuousOn X hX C.center i a t ha
  have hd : ∀ u ∈ Ico a t, ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasDerivWithinAt (f i) (f' i u) (Ici u) u :=
    fun u hu i _ => CapDrift.coordinate_hasDerivWithinAt X hX C.center i u (ha.trans hu.1)
  have hb : ∀ u ∈ Ico a t, (∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ f j u) →
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (∀ j ∈ (Finset.univ : Finset (Fin n)), f i u ≤ f j u) → 0 ≤ f' i u := by
    intro u _ hp i _ hmin
    exact ModelBounds.full_cap_minimum_vectorField_nonneg model β (X u) i C.center
      (hp i (Finset.mem_univ _)) (fun j => hmin j (Finset.mem_univ _))
  have hbound := MinimumBarrier.all_ge_of_active_nonneg Finset.univ hs f f'
    (AngularGeometry.cap_cos_radius_pos C) hstart hc hd hb
    (show t ∈ Icc a t from ⟨ht, le_rfl⟩)
  intro i
  exact (AngularGeometry.cap_mem_iff_inner C _).mpr (hbound i (Finset.mem_univ _))

/-- The terminal cap bounds the diameter by twice its radius for all later times. -/
theorem full_cap_diameter_bound (hn : 0 < n)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (C : Source.SphericalCap d) (a : ℝ) (ha : 0 ≤ a)
    (hinitial : ∀ i, X a i ∈ C.carrier) :
    ∀ t, a ≤ t → ∀ i j, Source.angularDist (X t i) (X t j) ≤ 2 * C.radius := by
  intro t ht i j
  have hi := full_cap_forward_invariant hn X hX C a ha hinitial t ht i
  have hj := full_cap_forward_invariant hn X hX C a ha hinitial t ht j
  change Source.angularDist (X t i) C.center ≤ C.radius at hi
  change Source.angularDist (X t j) C.center ≤ C.radius at hj
  calc
    _ ≤ Source.angularDist (X t i) C.center + Source.angularDist C.center (X t j) :=
      AngularGeometry.angularDist_triangle _ _ _
    _ ≤ 2 * C.radius := by rw [AngularGeometry.angularDist_comm C.center]; linarith

/-- Quantitative terminal energy control for every later original time. -/
theorem full_cap_energy_bound (hn : 0 < n) (hβ : 0 ≤ β)
    (X : ℝ → Source.Configuration n d) (hX : Source.Solves model β X)
    (C : Source.SphericalCap d) (a : ℝ) (ha : 0 ≤ a)
    (hinitial : ∀ i, X a i ∈ C.carrier) :
    ∀ t, a ≤ t → 0 ≤ 1 - Source.energy β (X t) ∧
      1 - Source.energy β (X t) ≤ 2 * β * C.radius ^ 2 := by
  intro t ht
  have h := EnergyEstimates.one_sub_energy_le_diameter hn β (2 * C.radius)
    hβ (by linarith [C.radius_nonneg]) (X t)
    (full_cap_diameter_bound hn X hX C a ha hinitial t ht)
  constructor
  · exact h.1
  · nlinarith [h.2]

end Metastability.CapInvariance
