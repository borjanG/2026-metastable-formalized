import Metastability.AngularGeometry

/-! Nonempty, bounded extrema for the literal source cap distances. -/

noncomputable section
open Set
namespace Metastability.CapDistances
variable {d : ℕ}

def values (C D : Source.SphericalCap d) : Set ℝ :=
  {r | ∃ x ∈ C.carrier, ∃ y ∈ D.carrier, r = Source.angularDist x y}

theorem values_nonempty (C D : Source.SphericalCap d) : (values C D).Nonempty :=
  ⟨Source.angularDist C.center D.center, C.center, AngularGeometry.cap_center_mem C,
    D.center, AngularGeometry.cap_center_mem D, rfl⟩

theorem values_bddBelow (C D : Source.SphericalCap d) : BddBelow (values C D) := by
  refine ⟨0, ?_⟩
  rintro r ⟨x, _, y, _, rfl⟩
  exact AngularGeometry.angularDist_nonneg x y

theorem values_bddAbove (C D : Source.SphericalCap d) : BddAbove (values C D) := by
  refine ⟨Real.pi, ?_⟩
  rintro r ⟨x, _, y, _, rfl⟩
  exact AngularGeometry.angularDist_le_pi x y

theorem capMinDistance_nonneg (C D : Source.SphericalCap d) :
    0 ≤ Source.capMinDistance C D := by
  apply le_csInf (values_nonempty C D)
  rintro r ⟨x, _, y, _, rfl⟩
  exact AngularGeometry.angularDist_nonneg x y

theorem capMaxDistance_le_pi (C D : Source.SphericalCap d) :
    Source.capMaxDistance C D ≤ Real.pi := by
  apply csSup_le (values_nonempty C D)
  rintro r ⟨x, _, y, _, rfl⟩
  exact AngularGeometry.angularDist_le_pi x y

theorem capMinDistance_le_angle (C D : Source.SphericalCap d)
    (x y : Source.Sphere d) (hx : x ∈ C.carrier) (hy : y ∈ D.carrier) :
    Source.capMinDistance C D ≤ Source.angularDist x y :=
  csInf_le (values_bddBelow C D) ⟨x, hx, y, hy, rfl⟩

theorem angle_le_capMaxDistance (C D : Source.SphericalCap d)
    (x y : Source.Sphere d) (hx : x ∈ C.carrier) (hy : y ∈ D.carrier) :
    Source.angularDist x y ≤ Source.capMaxDistance C D :=
  le_csSup (values_bddAbove C D) ⟨x, hx, y, hy, rfl⟩

theorem capMinDistance_le_capMaxDistance (C D : Source.SphericalCap d) :
    Source.capMinDistance C D ≤ Source.capMaxDistance C D :=
  (capMinDistance_le_angle C D C.center D.center
    (AngularGeometry.cap_center_mem C) (AngularGeometry.cap_center_mem D)).trans
    (angle_le_capMaxDistance C D C.center D.center
      (AngularGeometry.cap_center_mem C) (AngularGeometry.cap_center_mem D))

theorem capMaxDistance_nonneg (C D : Source.SphericalCap d) :
    0 ≤ Source.capMaxDistance C D :=
  (capMinDistance_nonneg C D).trans (capMinDistance_le_capMaxDistance C D)

theorem capMinDistance_le_pi (C D : Source.SphericalCap d) :
    Source.capMinDistance C D ≤ Real.pi :=
  (capMinDistance_le_capMaxDistance C D).trans (capMaxDistance_le_pi C D)

end Metastability.CapDistances
