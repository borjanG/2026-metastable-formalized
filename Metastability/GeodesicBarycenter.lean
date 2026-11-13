import Metastability.AngularGeometry

/-!
# Well-definedness and angle fractions of the literal spherical interpolation

The source formula is used unchanged. The non-antipodal hypothesis supplies the
nonzero sine denominator when the points differ, while the source's genuine
coincident-point case is handled separately.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace Metastability.GeodesicBarycenter

open Source AngularGeometry
variable {d : ℕ}

/-- The two prescribed angular portions sum to the total angle. -/
theorem weighted_angles_sum (a b θ : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a / (a + b) * θ + b / (a + b) * θ = θ := by
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  field_simp

/-- The scalar sine interpolation identity underlying both endpoint correlations. -/
theorem sine_interpolation_coordinate {θ s t : ℝ} (hsum : t + s = θ)
    (hθ : Real.sin θ ≠ 0) :
    Real.sin t / Real.sin θ + Real.sin s / Real.sin θ * Real.cos θ = Real.cos s := by
  have ht : t = θ - s := by linarith only [hsum]
  rw [ht, Real.sin_sub]
  field_simp
  ring

theorem sin_angularDist_ne_zero {u v : Sphere d} (hne : u ≠ v)
    (hθ : angularDist u v < Real.pi) : Real.sin (angularDist u v) ≠ 0 := by
  have hp : 0 < angularDist u v :=
    lt_of_le_of_ne (angularDist_nonneg u v)
      (fun he => hne ((angularDist_eq_zero_iff u v).mp he.symm))
  exact (Real.sin_pos_of_pos_of_lt_pi hp hθ).ne'

/-- Correlation with the first endpoint is the cosine of the b-fraction angle. -/
theorem inner_left (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Sphere d)
    (hθ : angularDist u v < Real.pi) :
    ⟪u.val, Source.geodesicBarycenter a b ha hb u v hθ⟫ =
      Real.cos (b / (a + b) * angularDist u v) := by
  by_cases he : u = v
  · subst v
    simp only [Source.geodesicBarycenter, if_true, angularDist_self, mul_zero,
      Real.cos_zero, real_inner_self_eq_norm_sq, u.property, one_pow]
  · rw [Source.geodesicBarycenter, if_neg he, inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_self_eq_norm_sq, u.property, one_pow, mul_one,
      ← cos_angularDist]
    exact sine_interpolation_coordinate (weighted_angles_sum a b _ ha hb)
      (sin_angularDist_ne_zero he hθ)

/-- Correlation with the second endpoint is the cosine of the a-fraction angle. -/
theorem inner_right (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Sphere d)
    (hθ : angularDist u v < Real.pi) :
    ⟪Source.geodesicBarycenter a b ha hb u v hθ, v.val⟫ =
      Real.cos (a / (a + b) * angularDist u v) := by
  by_cases he : u = v
  · subst v
    simp only [Source.geodesicBarycenter, if_true, angularDist_self, mul_zero,
      Real.cos_zero, real_inner_self_eq_norm_sq, u.property, one_pow]
  · rw [Source.geodesicBarycenter, if_neg he, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, v.property, one_pow, mul_one,
      ← cos_angularDist, add_comm]
    apply sine_interpolation_coordinate
    · linarith only [weighted_angles_sum a b (angularDist u v) ha hb]
    · exact sin_angularDist_ne_zero he hθ

/-- The manuscript's literal sine interpolation has unit norm. -/
theorem norm_geodesicBarycenter (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Sphere d)
    (hθ : angularDist u v < Real.pi) :
    ‖Source.geodesicBarycenter a b ha hb u v hθ‖ = 1 := by
  by_cases he : u = v
  · subst v
    simpa only [Source.geodesicBarycenter, if_true] using u.property
  have hs := sin_angularDist_ne_zero he hθ
  let z := Source.geodesicBarycenter a b ha hb u v hθ
  have hz : z = (Real.sin (a / (a + b) * angularDist u v) / Real.sin (angularDist u v)) • u.val +
      (Real.sin (b / (a + b) * angularDist u v) / Real.sin (angularDist u v)) • v.val := by
    exact if_neg he
  have hsq : ‖z‖ ^ 2 = 1 := by
    calc
      ‖z‖ ^ 2 = ⟪z, z⟫ := (real_inner_self_eq_norm_sq z).symm
      _ = (Real.sin (a / (a + b) * angularDist u v) / Real.sin (angularDist u v)) * ⟪u.val, z⟫ +
          (Real.sin (b / (a + b) * angularDist u v) / Real.sin (angularDist u v)) * ⟪v.val, z⟫ := by
        nth_rw 1 [hz]
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      _ = (Real.sin (a / (a + b) * angularDist u v) *
          Real.cos (b / (a + b) * angularDist u v) +
          Real.cos (a / (a + b) * angularDist u v) *
          Real.sin (b / (a + b) * angularDist u v)) / Real.sin (angularDist u v) := by
        rw [real_inner_comm z v.val, inner_left, inner_right]
        ring
      _ = 1 := by
        rw [← Real.sin_add, weighted_angles_sum a b _ ha hb, div_self hs]
  change ‖z‖ = 1
  nlinarith only [hsq, norm_nonneg z]

/-- The same source vector viewed on the sphere after proving its unit norm. -/
def point (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Sphere d)
    (hθ : angularDist u v < Real.pi) : Sphere d :=
  ⟨Source.geodesicBarycenter a b ha hb u v hθ, norm_geodesicBarycenter a b ha hb u v hθ⟩

theorem point_val (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Sphere d)
    (hθ : angularDist u v < Real.pi) :
    (point a b ha hb u v hθ).val = Source.geodesicBarycenter a b ha hb u v hθ := rfl

/-- Each weighted portion lies in the principal angular range. -/
theorem weighted_angle_bounds (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (u v : Sphere d) :
    0 ≤ b / (a + b) * angularDist u v ∧
      b / (a + b) * angularDist u v ≤ Real.pi := by
  have hp : 0 < b / (a + b) := div_pos hb (add_pos ha hb)
  have hle : b / (a + b) ≤ 1 := (div_le_one (add_pos ha hb)).mpr (by linarith only [ha])
  refine ⟨mul_nonneg hp.le (angularDist_nonneg u v), ?_⟩
  exact (mul_le_of_le_one_left (angularDist_nonneg u v) hle).trans (angularDist_le_pi u v)

/-- Distance from the first endpoint is the source fraction b/(a+b). -/
theorem angularDist_point_left (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Sphere d)
    (hθ : angularDist u v < Real.pi) :
    angularDist u (point a b ha hb u v hθ) = b / (a + b) * angularDist u v := by
  rw [angularDist, point_val, inner_left]
  exact Real.arccos_cos (weighted_angle_bounds a b ha hb u v).1
    (weighted_angle_bounds a b ha hb u v).2

/-- Distance to the second endpoint is the source fraction a/(a+b). -/
theorem angularDist_point_right (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Sphere d)
    (hθ : angularDist u v < Real.pi) :
    angularDist (point a b ha hb u v hθ) v = a / (a + b) * angularDist u v := by
  rw [angularDist, point_val, inner_right]
  have hr := weighted_angle_bounds b a hb ha u v
  rw [add_comm b a] at hr
  exact Real.arccos_cos hr.1 hr.2

theorem angularDist_add (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Sphere d)
    (hθ : angularDist u v < Real.pi) :
    angularDist u (point a b ha hb u v hθ) + angularDist (point a b ha hb u v hθ) v =
      angularDist u v := by
  rw [angularDist_point_left, angularDist_point_right]
  linarith only [weighted_angles_sum a b (angularDist u v) ha hb]

/-- The genuine coincident-point branch of the source interpolation. -/
theorem point_self (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u : Sphere d)
    (hθ : angularDist u u < Real.pi) : point a b ha hb u u hθ = u := by
  apply Subtype.ext
  simp only [point_val, Source.geodesicBarycenter, if_true]

/-- The prescribed weighted geodesic point stays in every strict-hemisphere cap
containing its endpoints. This supplies the cap step in recursive-center construction. -/
theorem point_mem_cap (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (u v : Sphere d)
    (hθ : angularDist u v < Real.pi) (C : SphericalCap d)
    (hu : u ∈ C.carrier) (hv : v ∈ C.carrier) : point a b ha hb u v hθ ∈ C.carrier := by
  by_cases he : u = v
  · subst v
    rwa [point_self]
  have hsin : 0 < Real.sin (angularDist u v) := by
    apply Real.sin_pos_of_pos_of_lt_pi _ hθ
    exact lt_of_le_of_ne (angularDist_nonneg u v)
      (fun hz => he ((angularDist_eq_zero_iff u v).mp hz.symm))
  let α := Real.sin (a / (a + b) * angularDist u v) / Real.sin (angularDist u v)
  let β := Real.sin (b / (a + b) * angularDist u v) / Real.sin (angularDist u v)
  have hα : 0 ≤ α := by
    have hr := weighted_angle_bounds b a hb ha u v
    rw [add_comm b a] at hr
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hr.1 hr.2) hsin.le
  have hβ : 0 ≤ β :=
    div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (weighted_angle_bounds a b ha hb u v).1
      (weighted_angle_bounds a b ha hb u v).2) hsin.le
  have hp : (point a b ha hb u v hθ).val = α • u.val + β • v.val := by
    exact if_neg he
  have hsum : 1 ≤ α + β := by
    calc
      1 = ‖(point a b ha hb u v hθ).val‖ := (point a b ha hb u v hθ).property.symm
      _ = ‖α • u.val + β • v.val‖ := by rw [hp]
      _ ≤ ‖α • u.val‖ + ‖β • v.val‖ := norm_add_le _ _
      _ = α + β := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hα, abs_of_nonneg hβ, u.property, v.property, mul_one, mul_one]
  apply (cap_mem_iff_inner C _).mpr
  rw [hp, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc
    Real.cos C.radius ≤ (α + β) * Real.cos C.radius :=
      le_mul_of_one_le_left (cap_cos_radius_pos C).le hsum
    _ = α * Real.cos C.radius + β * Real.cos C.radius := by ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left ((cap_mem_iff_inner C u).mp hu) hα)
      (mul_le_mul_of_nonneg_left ((cap_mem_iff_inner C v).mp hv) hβ)

end Metastability.GeodesicBarycenter
