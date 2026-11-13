import Metastability.AngularGeometry

/-!
# Euclidean block means inside a spherical cap

The mean is defined on nonempty blocks. Its nonvanishing follows from the
source cap condition, and the normalized mean is constructed using that proof.
There is no zero-mean fallback and no nonvanishing premise in the source-facing
cap lemmas.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Metastability.BlockGeometry

open Source AngularGeometry
variable {n d : ℕ}

/-- The literal Euclidean average of a nonempty block of sphere-valued particles. -/
def blockMean (A : Block n) (_hA : A.Nonempty) (x : Configuration n d) : Vector d :=
  (A.card : ℝ)⁻¹ • ∑ i ∈ A, (x i).val

theorem card_pos (A : Block n) (hA : A.Nonempty) : (0 : ℝ) < A.card := by
  exact_mod_cast Finset.card_pos.mpr hA

theorem blockMean_inner (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    (v : Vector d) :
    ⟪blockMean A hA x, v⟫ = (A.card : ℝ)⁻¹ * ∑ i ∈ A, ⟪(x i).val, v⟫ := by
  simp only [blockMean, real_inner_smul_left, sum_inner]

theorem blockMean_norm_le_one (A : Block n) (hA : A.Nonempty) (x : Configuration n d) :
    ‖blockMean A hA x‖ ≤ 1 := by
  have hc := card_pos A hA
  have hs : ‖∑ i ∈ A, (x i).val‖ ≤ (A.card : ℝ) := by
    calc
      _ ≤ ∑ i ∈ A, ‖(x i).val‖ := norm_sum_le A (fun i => (x i).val)
      _ = A.card := by
        simp only [show ∀ i, ‖(x i).val‖ = 1 from fun i => (x i).property,
          Finset.sum_const, nsmul_eq_mul, mul_one]
  calc
    ‖blockMean A hA x‖ = (A.card : ℝ)⁻¹ * ‖∑ i ∈ A, (x i).val‖ := by
      rw [blockMean, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    _ ≤ (A.card : ℝ)⁻¹ * A.card := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hc.le)
    _ = 1 := inv_mul_cancel₀ hc.ne'

/-- The cap's positive cosine is retained under Euclidean averaging. -/
theorem cos_radius_le_inner_blockMean (A : Block n) (hA : A.Nonempty)
    (x : Configuration n d) (C : SphericalCap d)
    (hcap : ∀ i ∈ A, x i ∈ C.carrier) :
    Real.cos C.radius ≤ ⟪blockMean A hA x, C.center.val⟫ := by
  have hc := card_pos A hA
  have hs : (A.card : ℝ) * Real.cos C.radius ≤ ∑ i ∈ A, ⟪(x i).val, C.center.val⟫ := by
    calc
      _ = ∑ _i ∈ A, Real.cos C.radius := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun i hi => (cap_mem_iff_inner C (x i)).mp (hcap i hi)
  rw [blockMean_inner]
  calc
    Real.cos C.radius = (A.card : ℝ)⁻¹ * ((A.card : ℝ) * Real.cos C.radius) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hc.le)

theorem cos_radius_le_norm_blockMean (A : Block n) (hA : A.Nonempty)
    (x : Configuration n d) (C : SphericalCap d)
    (hcap : ∀ i ∈ A, x i ∈ C.carrier) :
    Real.cos C.radius ≤ ‖blockMean A hA x‖ := by
  calc
    _ ≤ ⟪blockMean A hA x, C.center.val⟫ := cos_radius_le_inner_blockMean A hA x C hcap
    _ ≤ ‖blockMean A hA x‖ * ‖C.center.val‖ := real_inner_le_norm _ _
    _ = ‖blockMean A hA x‖ := by rw [C.center.property, mul_one]

theorem blockMean_ne_zero (A : Block n) (hA : A.Nonempty)
    (x : Configuration n d) (C : SphericalCap d)
    (hcap : ∀ i ∈ A, x i ∈ C.carrier) : blockMean A hA x ≠ 0 := by
  have hp := (cap_cos_radius_pos C).trans_le (cos_radius_le_norm_blockMean A hA x C hcap)
  exact norm_pos_iff.mp hp

/-- The normalized block mean, with nonvanishing established from the cap data. -/
def normalizedMean (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    (C : SphericalCap d) (hcap : ∀ i ∈ A, x i ∈ C.carrier) : Sphere d :=
  ⟨‖blockMean A hA x‖⁻¹ • blockMean A hA x,
    norm_smul_inv_norm (blockMean_ne_zero A hA x C hcap)⟩

theorem normalizedMean_val (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    (C : SphericalCap d) (hcap : ∀ i ∈ A, x i ∈ C.carrier) :
    (normalizedMean A hA x C hcap).val = ‖blockMean A hA x‖⁻¹ • blockMean A hA x := rfl

/-- The normalized mean does not depend on which containing cap proves nonvanishing. -/
theorem normalizedMean_cap_independent (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    (C D : SphericalCap d) (hC : ∀ i ∈ A, x i ∈ C.carrier)
    (hD : ∀ i ∈ A, x i ∈ D.carrier) :
    normalizedMean A hA x C hC = normalizedMean A hA x D hD := Subtype.ext rfl

/-- Normalizing the Euclidean average keeps it inside the same strict-hemisphere cap. -/
theorem normalizedMean_mem_cap (A : Block n) (hA : A.Nonempty)
    (x : Configuration n d) (C : SphericalCap d)
    (hcap : ∀ i ∈ A, x i ∈ C.carrier) : normalizedMean A hA x C hcap ∈ C.carrier := by
  apply (cap_mem_iff_inner C _).mpr
  rw [normalizedMean_val, real_inner_smul_left, ← div_eq_inv_mul]
  have hp : 0 < ‖blockMean A hA x‖ :=
    norm_pos_iff.mpr (blockMean_ne_zero A hA x C hcap)
  apply (le_div_iff₀ hp).mpr
  calc
    Real.cos C.radius * ‖blockMean A hA x‖ ≤ Real.cos C.radius * 1 :=
      mul_le_mul_of_nonneg_left (blockMean_norm_le_one A hA x) (cap_cos_radius_pos C).le
    _ ≤ ⟪blockMean A hA x, C.center.val⟫ := by
      rw [mul_one]
      exact cos_radius_le_inner_blockMean A hA x C hcap

/-- A block of angular diameter below a hemisphere supplies its own containing cap. -/
theorem exists_cap_of_diameter (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    {ε : ℝ} (hεπ : ε < Real.pi / 2)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε) :
    ∃ C : SphericalCap d, C.radius = ε ∧ ∀ i ∈ A, x i ∈ C.carrier := by
  obtain ⟨i₀, hi₀⟩ := hA
  have hε0 : 0 ≤ ε := by simpa only [angularDist_self] using hdiam i₀ hi₀ i₀ hi₀
  exact ⟨⟨x i₀, ε, hε0, hεπ⟩, rfl, fun i hi => hdiam i hi i₀ hi₀⟩

/-- Nonvanishing follows from a small diameter alone; it is not a new premise. -/
theorem blockMean_ne_zero_of_diameter (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    {ε : ℝ} (hεπ : ε < Real.pi / 2)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε) :
    blockMean A hA x ≠ 0 := by
  obtain ⟨C, _, hcap⟩ := exists_cap_of_diameter A hA x hεπ hdiam
  exact blockMean_ne_zero A hA x C hcap

/-- A normalized mean belongs to every containing strict-hemisphere cap. -/
theorem normalizedMean_mem_any_cap (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    (C D : SphericalCap d) (hC : ∀ i ∈ A, x i ∈ C.carrier)
    (hD : ∀ i ∈ A, x i ∈ D.carrier) : normalizedMean A hA x C hC ∈ D.carrier := by
  rw [normalizedMean_cap_independent A hA x C D hC hD]
  exact normalizedMean_mem_cap A hA x D hD

/-- Small angular diameter bounds every particle's angle to the normalized mean. -/
theorem angularDist_normalizedMean_le_of_diameter
    (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    (C : SphericalCap d) (hcap : ∀ i ∈ A, x i ∈ C.carrier)
    {ε : ℝ} (hεπ : ε < Real.pi / 2)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε)
    {i : Fin n} (hi : i ∈ A) :
    angularDist (x i) (normalizedMean A hA x C hcap) ≤ ε := by
  have hε0 : 0 ≤ ε := by simpa only [angularDist_self] using hdiam i hi i hi
  let D : SphericalCap d := ⟨x i, ε, hε0, hεπ⟩
  have hD : ∀ j ∈ A, x j ∈ D.carrier := fun j hj => hdiam j hj i hi
  have hm := normalizedMean_mem_any_cap A hA x C D hcap hD
  change angularDist (normalizedMean A hA x C hcap) (x i) ≤ ε at hm
  rwa [angularDist_comm] at hm

/-- The first estimate of tight-block geometry, with explicit constant one. -/
theorem norm_sub_normalizedMean_le_of_diameter
    (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    (C : SphericalCap d) (hcap : ∀ i ∈ A, x i ∈ C.carrier)
    {ε : ℝ} (hεπ : ε < Real.pi / 2)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε)
    {i : Fin n} (hi : i ∈ A) :
    ‖(x i).val - (normalizedMean A hA x C hcap).val‖ ≤ ε :=
  (norm_sub_le_angularDist _ _).trans
    (angularDist_normalizedMean_le_of_diameter A hA x C hcap hεπ hdiam hi)

/-- The inner-product deficit is quadratic in the angular diameter. -/
theorem one_sub_inner_normalizedMean_le_of_diameter
    (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    (C : SphericalCap d) (hcap : ∀ i ∈ A, x i ∈ C.carrier)
    {ε : ℝ} (hεπ : ε < Real.pi / 2)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε)
    {i : Fin n} (hi : i ∈ A) :
    1 - ⟪(x i).val, (normalizedMean A hA x C hcap).val⟫ ≤ ε ^ 2 / 2 := by
  have hn := norm_sub_normalizedMean_le_of_diameter A hA x C hcap hεπ hdiam hi
  have hs := norm_sub_sq_real (x i).val (normalizedMean A hA x C hcap).val
  rw [(x i).property, (normalizedMean A hA x C hcap).property, one_pow] at hs
  have hε0 := (norm_nonneg _).trans hn
  nlinarith only [hs, hn, hε0, norm_nonneg ((x i).val - (normalizedMean A hA x C hcap).val)]

/-- The Euclidean mean's norm deficit is quadratic in the angular diameter. -/
theorem abs_norm_blockMean_sub_one_le_of_diameter
    (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    {ε : ℝ} (hεπ : ε < Real.pi / 2)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε) :
    |‖blockMean A hA x‖ - 1| ≤ ε ^ 2 / 2 := by
  obtain ⟨C, hC, hcap⟩ := exists_cap_of_diameter A hA x hεπ hdiam
  have hl := cos_radius_le_norm_blockMean A hA x C hcap
  rw [hC] at hl
  have hc : 1 - ε ^ 2 / 2 ≤ Real.cos ε := Real.one_sub_sq_div_two_le_cos
  rw [abs_of_nonpos (sub_nonpos.mpr (blockMean_norm_le_one A hA x))]
  linarith only [hl, hc]

/-- Existence and the three explicit tight-block estimates, derived solely from diameter. -/
theorem exists_normalizedMean_of_diameter
    (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    {ε : ℝ} (hεπ : ε < Real.pi / 2)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε) :
    blockMean A hA x ≠ 0 ∧ ∃ z : Sphere d,
      z.val = ‖blockMean A hA x‖⁻¹ • blockMean A hA x ∧
      (∀ i ∈ A, ‖(x i).val - z.val‖ ≤ ε ∧ 1 - ⟪(x i).val, z.val⟫ ≤ ε ^ 2 / 2) ∧
      |‖blockMean A hA x‖ - 1| ≤ ε ^ 2 / 2 := by
  obtain ⟨C, _, hcap⟩ := exists_cap_of_diameter A hA x hεπ hdiam
  refine ⟨blockMean_ne_zero A hA x C hcap, normalizedMean A hA x C hcap, rfl, ?_,
    abs_norm_blockMean_sub_one_le_of_diameter A hA x hεπ hdiam⟩
  intro i hi
  exact ⟨norm_sub_normalizedMean_le_of_diameter A hA x C hcap hεπ hdiam hi,
    one_sub_inner_normalizedMean_le_of_diameter A hA x C hcap hεπ hdiam hi⟩

/-- Replacing each of two unit vectors costs at most the sum of its chordal errors. -/
theorem abs_inner_sub_inner_le (x y u v : Sphere d) :
    |⟪x.val, y.val⟫ - ⟪u.val, v.val⟫| ≤ ‖x.val - u.val‖ + ‖y.val - v.val‖ := by
  have he : ⟪x.val, y.val⟫ - ⟪u.val, v.val⟫ =
      ⟪x.val - u.val, y.val⟫ + ⟪u.val, y.val - v.val⟫ := by
    rw [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |⟪x.val - u.val, y.val⟫| + |⟪u.val, y.val - v.val⟫| := abs_add_le _ _
    _ ≤ ‖x.val - u.val‖ * ‖y.val‖ + ‖u.val‖ * ‖y.val - v.val‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = _ := by rw [y.property, u.property, mul_one, one_mul]

/-- Tangent projection varies by at most twice the chordal change of its base point. -/
theorem norm_projectTangent_sub_le (x u v : Sphere d) :
    ‖projectTangent x v.val - projectTangent u v.val‖ ≤ 2 * ‖x.val - u.val‖ := by
  have he : projectTangent x v.val - projectTangent u v.val =
      (-⟪x.val, v.val⟫) • (x.val - u.val) - ⟪x.val - u.val, v.val⟫ • u.val := by
    simp only [projectTangent, inner_sub_left, smul_sub, sub_smul, neg_smul]
    abel
  have hi : |⟪x.val, v.val⟫| ≤ 1 := by
    simpa only [x.property, v.property, mul_one] using abs_real_inner_le_norm x.val v.val
  have hd : |⟪x.val - u.val, v.val⟫| ≤ ‖x.val - u.val‖ := by
    simpa only [v.property, mul_one] using abs_real_inner_le_norm (x.val - u.val) v.val
  rw [he]
  calc
    _ ≤ ‖(-⟪x.val, v.val⟫) • (x.val - u.val)‖ + ‖⟪x.val - u.val, v.val⟫ • u.val‖ :=
      norm_sub_le _ _
    _ = |⟪x.val, v.val⟫| * ‖x.val - u.val‖ + |⟪x.val - u.val, v.val⟫| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, u.property, mul_one]
    _ ≤ 1 * ‖x.val - u.val‖ + ‖x.val - u.val‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hi (norm_nonneg _)) hd
    _ = _ := by ring

/-- The two-block scalar-product error in tight geometry, with explicit constant two.
Disjointness is unnecessary for this estimate. -/
theorem abs_inner_sub_blockCenters_le_of_diameter
    (A D : Block n) (hA : A.Nonempty) (hD : D.Nonempty) (x : Configuration n d)
    (C F : SphericalCap d) (hC : ∀ i ∈ A, x i ∈ C.carrier)
    (hF : ∀ j ∈ D, x j ∈ F.carrier) {ε : ℝ} (hεπ : ε < Real.pi / 2)
    (hdiamA : ∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε)
    (hdiamD : ∀ i ∈ D, ∀ j ∈ D, angularDist (x i) (x j) ≤ ε)
    {i j : Fin n} (hi : i ∈ A) (hj : j ∈ D) :
    |⟪(x i).val, (x j).val⟫ -
      ⟪(normalizedMean A hA x C hC).val, (normalizedMean D hD x F hF).val⟫| ≤ 2 * ε := by
  calc
    _ ≤ ‖(x i).val - (normalizedMean A hA x C hC).val‖ +
        ‖(x j).val - (normalizedMean D hD x F hF).val‖ := abs_inner_sub_inner_le _ _ _ _
    _ ≤ ε + ε := add_le_add
      (norm_sub_normalizedMean_le_of_diameter A hA x C hC hεπ hdiamA hi)
      (norm_sub_normalizedMean_le_of_diameter D hD x F hF hεπ hdiamD hj)
    _ = _ := by ring

/-- The projection error in tight geometry, with explicit constant two. -/
theorem norm_projectTangent_sub_blockCenter_le_of_diameter
    (A : Block n) (hA : A.Nonempty) (x : Configuration n d)
    (C : SphericalCap d) (hcap : ∀ i ∈ A, x i ∈ C.carrier)
    {ε : ℝ} (hεπ : ε < Real.pi / 2)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε)
    {i : Fin n} (hi : i ∈ A) (v : Sphere d) :
    ‖projectTangent (x i) v.val - projectTangent (normalizedMean A hA x C hcap) v.val‖ ≤ 2 * ε :=
  (norm_projectTangent_sub_le _ _ _).trans
    (mul_le_mul_of_nonneg_left
      (norm_sub_normalizedMean_le_of_diameter A hA x C hcap hεπ hdiam hi) (by norm_num))

end Metastability.BlockGeometry
