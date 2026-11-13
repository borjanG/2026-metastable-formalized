import Metastability.BarycenterFormula

/-! Exact cancellation for the source weighted geodesic point, without any
assumed invariant or regularity at the diagonal. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.BarycenterDifferential
open Source AngularGeometry BarycenterFormula
variable {d : ℕ}

theorem correlationVelocity_pair (p q : Sphere d) (α γ : ℝ) :
    correlationVelocity p.val q.val (α • projectTangent p q.val) (γ • projectTangent q p.val) =
      (α + γ) * (1 - ⟪p.val, q.val⟫ ^ 2) := by
  simp only [correlationVelocity, projectTangent, real_inner_smul_left, inner_smul_right,
    inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq, p.property, q.property,
    one_pow, real_inner_comm q.val p.val]
  ring

theorem sine_sq (p q : Sphere d) :
    1 - ⟪p.val, q.val⟫ ^ 2 = Real.sin (angularDist p q) ^ 2 := by
  have hh := Real.sin_sq_add_cos_sq (angularDist p q)
  rw [cos_angularDist] at hh
  linarith only [hh]

theorem angleVelocity_pair (p q : Sphere d) (α γ : ℝ)
    (hneq : p ≠ q) (hθ : angularDist p q < Real.pi) :
    angleVelocity p.val q.val (α • projectTangent p q.val) (γ • projectTangent q p.val) =
      -(α + γ) * Real.sin (angularDist p q) := by
  have hs := GeodesicBarycenter.sin_angularDist_ne_zero hneq hθ
  rw [angleVelocity, correlationVelocity_pair, sine_sq]
  change -((α + γ) * Real.sin (angularDist p q) ^ 2) / Real.sin (angularDist p q) = _
  field_simp

theorem projection_pair_variation (p q : Sphere d) (α γ : ℝ) :
    γ • projectTangent q p.val -
      (correlationVelocity p.val q.val (α • projectTangent p q.val) (γ • projectTangent q p.val) • p.val +
        ⟪p.val, q.val⟫ • (α • projectTangent p q.val)) =
      (-α * Real.sin (angularDist p q) ^ 2) • p.val -
        ((α + γ) * ⟪p.val, q.val⟫) • projectTangent p q.val := by
  rw [correlationVelocity_pair, ← sine_sq]
  simp only [projectTangent, real_inner_comm q.val p.val]
  module

/-- The pair vector field acts on the interpolation by the mismatch of its
weighted angular velocities. This exact formula gives cancellation. -/
theorem differential_pair (s : ℝ) (p q : Sphere d) (α γ : ℝ)
    (hneq : p ≠ q) (hθ : angularDist p q < Real.pi) :
    differential s p.val q.val (α • projectTangent p q.val) (γ • projectTangent q p.val) =
      (α - s * (α + γ)) •
        ((-Real.sin (s * angularDist p q) * Real.sin (angularDist p q)) • p.val +
          Real.cos (s * angularDist p q) • projectTangent p q.val) := by
  have hs := GeodesicBarycenter.sin_angularDist_ne_zero hneq hθ
  dsimp only [differential]
  rw [angleVelocity_pair p q α γ hneq hθ, projection_pair_variation]
  change (-(Real.sin (s * angularDist p q) * (s * (-(α + γ) * Real.sin (angularDist p q))))) • p.val +
      Real.cos (s * angularDist p q) • (α • projectTangent p q.val) +
      (ratioDerivative s (angularDist p q) * (-(α + γ) * Real.sin (angularDist p q))) • projectTangent p q.val +
      (Real.sin (s * angularDist p q) / Real.sin (angularDist p q)) •
        ((-α * Real.sin (angularDist p q) ^ 2) • p.val -
          ((α + γ) * ⟪p.val, q.val⟫) • projectTangent p q.val) = _
  have hratio : ratioDerivative s (angularDist p q) * (-(α + γ) * Real.sin (angularDist p q)) =
      -(α + γ) * s * Real.cos (s * angularDist p q) +
        (α + γ) * Real.sin (s * angularDist p q) / Real.sin (angularDist p q) * ⟪p.val, q.val⟫ := by
    rw [ratioDerivative, cos_angularDist]
    field_simp
    ring
  have hsquare : Real.sin (s * angularDist p q) / Real.sin (angularDist p q) *
      (-α * Real.sin (angularDist p q) ^ 2) = -α * Real.sin (s * angularDist p q) * Real.sin (angularDist p q) := by
    field_simp
  rw [hratio, smul_sub]
  simp only [smul_smul]
  rw [hsquare]
  module

/-- The source weight balance is precisely the vanishing mismatch. -/
theorem differential_pair_eq_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p q : Sphere d) (α γ : ℝ) (hbalance : a * α = b * γ)
    (hneq : p ≠ q) (hθ : angularDist p q < Real.pi) :
    differential (b / (a + b)) p.val q.val
      (α • projectTangent p q.val) (γ • projectTangent q p.val) = 0 := by
  rw [differential_pair _ p q α γ hneq hθ]
  have hm : α - b / (a + b) * (α + γ) = 0 := by
    have hab : a + b ≠ 0 := (add_pos ha hb).ne'
    field_simp
    nlinarith only [hbalance]
  rw [hm, zero_smul]

end Metastability.BarycenterDifferential
