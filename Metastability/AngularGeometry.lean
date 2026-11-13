import Metastability.SourceDefinitions
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The source angular distance and spherical caps

The angular distance remains the manuscript's `arccos` of the inner product.
These lemmas identify it with Mathlib's angle and establish its basic laws;
no ambient chordal metric is substituted for it.
-/

noncomputable section
open scoped RealInnerProductSpace
open Set

namespace Metastability.AngularGeometry

open Source
variable {d : ℕ}

theorem angularDist_eq_angle (x y : Sphere d) :
    angularDist x y = InnerProductGeometry.angle x.val y.val := by
  simp only [angularDist, InnerProductGeometry.angle, x.property, y.property, mul_one, div_one]

theorem angularDist_nonneg (x y : Sphere d) : 0 ≤ angularDist x y :=
  Real.arccos_nonneg _

theorem angularDist_le_pi (x y : Sphere d) : angularDist x y ≤ Real.pi :=
  Real.arccos_le_pi _

theorem angularDist_self (x : Sphere d) : angularDist x x = 0 := by
  simp only [angularDist, real_inner_self_eq_norm_sq, x.property, one_pow, Real.arccos_one]

theorem angularDist_comm (x y : Sphere d) : angularDist x y = angularDist y x := by
  simp only [angularDist, real_inner_comm x.val y.val]

theorem angularDist_eq_zero_iff (x y : Sphere d) : angularDist x y = 0 ↔ x = y := by
  rw [angularDist, Real.arccos_eq_zero]
  constructor
  · intro h
    exact Subtype.ext ((inner_eq_one_iff_of_norm_eq_one x.property y.property).mp
      (le_antisymm (real_inner_le_one_of_norm_eq_one x.property y.property) h))
  · rintro rfl
    rw [real_inner_self_eq_norm_sq, x.property, one_pow]

theorem angularDist_triangle (x y z : Sphere d) :
    angularDist x z ≤ angularDist x y + angularDist y z := by
  simp only [angularDist_eq_angle]
  exact InnerProductGeometry.angle_le_angle_add_angle x.val y.val z.val

theorem cos_angularDist (x y : Sphere d) : Real.cos (angularDist x y) = ⟪x.val, y.val⟫ :=
  Real.cos_arccos (neg_one_le_real_inner_of_norm_eq_one x.property y.property)
    (real_inner_le_one_of_norm_eq_one x.property y.property)

theorem continuous_angularDist :
    Continuous (fun p : Sphere d × Sphere d => angularDist p.1 p.2) := by
  exact Real.continuous_arccos.comp
    ((continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd))

theorem continuous_angularDist_left (y : Sphere d) :
    Continuous (fun x : Sphere d => angularDist x y) :=
  Real.continuous_arccos.comp (continuous_subtype_val.inner continuous_const)

theorem continuous_angularDist_right (x : Sphere d) : Continuous (angularDist x) :=
  Real.continuous_arccos.comp (continuous_const.inner continuous_subtype_val)

/-- Exact conversion of a cap inequality to an inner-product inequality. -/
theorem angularDist_le_iff_inner (x y : Sphere d) {r : ℝ} (hr0 : 0 ≤ r) (hrπ : r ≤ Real.pi) :
    angularDist x y ≤ r ↔ Real.cos r ≤ ⟪x.val, y.val⟫ := by
  constructor
  · intro h
    simpa only [cos_angularDist] using
      Real.cos_le_cos_of_nonneg_of_le_pi (angularDist_nonneg x y) hrπ h
  · intro h
    have ha := Real.arccos_le_arccos h
    simpa only [Real.arccos_cos hr0 hrπ] using ha

theorem cap_mem_iff_inner (C : SphericalCap d) (x : Sphere d) :
    x ∈ C.carrier ↔ Real.cos C.radius ≤ ⟪x.val, C.center.val⟫ :=
  angularDist_le_iff_inner x C.center C.radius_nonneg
    (C.radius_lt_half_pi.le.trans (by linarith only [Real.pi_pos]))

theorem cap_center_mem (C : SphericalCap d) : C.center ∈ C.carrier := by
  change angularDist C.center C.center ≤ C.radius
  rw [angularDist_self]
  exact C.radius_nonneg

theorem cap_nonempty (C : SphericalCap d) : C.carrier.Nonempty :=
  ⟨C.center, cap_center_mem C⟩

theorem cap_isClosed (C : SphericalCap d) : IsClosed C.carrier :=
  isClosed_le (continuous_angularDist_left C.center) continuous_const

theorem cap_cos_radius_pos (C : SphericalCap d) : 0 < Real.cos C.radius :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith only [C.radius_nonneg, Real.pi_pos], C.radius_lt_half_pi⟩

/-- Chordal distance is bounded by the source angular distance. -/
theorem norm_sub_le_angularDist (x y : Sphere d) : ‖x.val - y.val‖ ≤ angularDist x y := by
  have hs := norm_sub_sq_real x.val y.val
  rw [x.property, y.property, one_pow] at hs
  have hc : 1 - angularDist x y ^ 2 / 2 ≤ Real.cos (angularDist x y) :=
    Real.one_sub_sq_div_two_le_cos
  rw [cos_angularDist] at hc
  nlinarith only [hs, hc, norm_nonneg (x.val - y.val), angularDist_nonneg x y]

end Metastability.AngularGeometry
