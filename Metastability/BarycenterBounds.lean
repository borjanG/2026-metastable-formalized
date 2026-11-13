import Metastability.BarycenterDifferential

/-! A quantitative differential bound sufficient on the mesoscopic active
window. The reciprocal sine loss cancels the relative tangent-velocity error. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.BarycenterBounds
open Source AngularGeometry BarycenterFormula BarycenterDifferential
variable {d : ℕ}

theorem abs_inner_tangent_le (p q : Sphere d) (v : Vector d)
    (hv : ⟪p.val, v⟫ = 0) :
    |⟪v, q.val⟫| ≤ ‖v‖ * Real.sin (angularDist p q) := by
  have hv' : ⟪v, p.val⟫ = 0 := by rw [real_inner_comm]; exact hv
  have he : ⟪v, projectTangent p q.val⟫ = ⟪v, q.val⟫ := by
    simp only [projectTangent, inner_sub_right, inner_smul_right, hv', mul_zero, sub_zero]
  have hh := abs_real_inner_le_norm v (projectTangent p q.val)
  rwa [he, norm_projectTangent] at hh

theorem abs_correlationVelocity_le (p q : Sphere d) (v w : Vector d)
    (hv : ⟪p.val, v⟫ = 0) (hw : ⟪q.val, w⟫ = 0) :
    |correlationVelocity p.val q.val v w| ≤
      Real.sin (angularDist p q) * (‖v‖ + ‖w‖) := by
  have h1 := abs_inner_tangent_le p q v hv
  have h2 := abs_inner_tangent_le q p w hw
  have he : ⟪w, p.val⟫ = ⟪p.val, w⟫ := real_inner_comm _ _
  rw [he, angularDist_comm q p] at h2
  exact (abs_add_le _ _).trans (by nlinarith only [h1, h2])

theorem abs_angleVelocity_le (p q : Sphere d) (v w : Vector d)
    (hv : ⟪p.val, v⟫ = 0) (hw : ⟪q.val, w⟫ = 0)
    (hneq : p ≠ q) (hθ : angularDist p q < Real.pi) :
    |angleVelocity p.val q.val v w| ≤ ‖v‖ + ‖w‖ := by
  have hpos : 0 < Real.sin (angularDist p q) := Real.sin_pos_of_pos_of_lt_pi
    (lt_of_le_of_ne (angularDist_nonneg p q) (fun hz => hneq ((angularDist_eq_zero_iff p q).mp hz.symm))) hθ
  rw [angleVelocity, abs_div, abs_neg]
  change |correlationVelocity p.val q.val v w| / |Real.sin (angularDist p q)| ≤ _
  rw [abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  nlinarith only [abs_correlationVelocity_le p q v w hv hw]

theorem ratioDerivative_bound (s θ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hθ : 0 < Real.sin θ) :
    |ratioDerivative s θ| * Real.sin θ ^ 2 ≤ 2 := by
  rw [ratioDerivative, abs_div, abs_of_pos (sq_pos_of_pos hθ), div_mul_cancel₀ _ (sq_pos_of_pos hθ).ne']
  have h1 : |s * Real.cos (s * θ) * Real.sin θ| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_pos hθ]
    calc
      _ ≤ 1 * 1 * 1 := mul_le_mul
        (mul_le_mul hs1 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one)
        (Real.sin_le_one θ) hθ.le (by norm_num)
      _ = 1 := by norm_num
  have h2 : |Real.sin (s * θ) * Real.cos θ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  exact (abs_sub _ _).trans (by linarith only [h1, h2])

/-- Multiplying by sin(theta) gives a uniform tangent differential bound.
The angle need not stay away from zero. -/
theorem sine_mul_norm_differential_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (p q : Sphere d) (v w : Vector d)
    (hv : ⟪p.val, v⟫ = 0) (hw : ⟪q.val, w⟫ = 0)
    (hneq : p ≠ q) (hθ : angularDist p q < Real.pi) :
    Real.sin (angularDist p q) * ‖differential s p.val q.val v w‖ ≤ 6 * (‖v‖ + ‖w‖) := by
  let θ := angularDist p q
  let S := Real.sin θ
  let E := ‖v‖ + ‖w‖
  have hS : 0 < S := Real.sin_pos_of_pos_of_lt_pi
    (lt_of_le_of_ne (angularDist_nonneg p q) (fun hz => hneq ((angularDist_eq_zero_iff p q).mp hz.symm))) hθ
  have hS1 : S ≤ 1 := Real.sin_le_one θ
  have hE : 0 ≤ E := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hθv := abs_angleVelocity_le p q v w hv hw hneq hθ
  have hρv := abs_correlationVelocity_le p q v w hv hw
  have hρabs : |⟪p.val, q.val⟫| ≤ 1 := by
    simpa only [p.property, q.property, mul_one] using abs_real_inner_le_norm p.val q.val
  have hrv := ratioDerivative_bound s θ hs0 hs1 hS
  have hratio : |Real.sin (s * θ) / S| * S ≤ 1 := by
    rw [abs_div, abs_of_pos hS, div_mul_cancel₀ _ hS.ne']
    exact Real.abs_sin_le_one _
  have hρE : |correlationVelocity p.val q.val v w| ≤ E := by
    exact hρv.trans (mul_le_of_le_one_left hE hS1)
  have horth : ‖w - (correlationVelocity p.val q.val v w • p.val + ⟪p.val, q.val⟫ • v)‖ ≤ 2 * E := by
    calc
      _ ≤ ‖w‖ + (‖correlationVelocity p.val q.val v w • p.val‖ + ‖⟪p.val, q.val⟫ • v‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ = ‖w‖ + (|correlationVelocity p.val q.val v w| + |⟪p.val, q.val⟫| * ‖v‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, p.property, mul_one]
      _ ≤ ‖w‖ + (E + 1 * ‖v‖) := by gcongr
      _ = 2 * E := by dsimp only [E]; ring
  let A : Vector d := (-(Real.sin (s * θ) * (s * angleVelocity p.val q.val v w))) • p.val
  let B : Vector d := Real.cos (s * θ) • v
  let C : Vector d := (ratioDerivative s θ * angleVelocity p.val q.val v w) • projectTangent p q.val
  let D : Vector d := (Real.sin (s * θ) / S) •
    (w - (correlationVelocity p.val q.val v w • p.val + ⟪p.val, q.val⟫ • v))
  have hA : ‖A‖ ≤ E := by
    dsimp only [A]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_of_nonneg hs0, p.property, mul_one]
    calc
      _ ≤ 1 * (1 * E) := by gcongr; exact Real.abs_sin_le_one _
      _ = E := by ring
  have hB : ‖B‖ ≤ ‖v‖ := by
    dsimp only [B]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  have hC : S * ‖C‖ ≤ 2 * E := by
    dsimp only [C]
    rw [norm_smul, Real.norm_eq_abs, abs_mul, norm_projectTangent]
    change S * (|ratioDerivative s θ| * |angleVelocity p.val q.val v w| * S) ≤ _
    have hh := mul_le_mul hrv hθv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hh]
  have hD : S * ‖D‖ ≤ 2 * E := by
    dsimp only [D]
    rw [norm_smul, Real.norm_eq_abs]
    have hh := mul_le_mul hratio horth (norm_nonneg _) zero_le_one
    nlinarith only [hh]
  have hsum : ‖A + B + C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  have hA' : S * ‖A‖ ≤ E := (mul_le_mul_of_nonneg_left hA hS.le).trans (mul_le_of_le_one_left hE hS1)
  have hB' : S * ‖B‖ ≤ E := by
    have hh := hB.trans (show ‖v‖ ≤ E by dsimp only [E]; exact le_add_of_nonneg_right (norm_nonneg _))
    exact (mul_le_mul_of_nonneg_left hh hS.le).trans (mul_le_of_le_one_left hE hS1)
  have htotal := mul_le_mul_of_nonneg_left hsum hS.le
  change S * ‖A + B + C + D‖ ≤ 6 * E
  nlinarith only [htotal, hA', hB', hC, hD]

/-- Exact cancellation leaves only the two tangent-velocity errors. -/
theorem sine_mul_norm_differential_error_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p q : Sphere d) (v w : Vector d) (α γ : ℝ)
    (hbalance : a * α = b * γ)
    (hv : ⟪p.val, v⟫ = 0) (hw : ⟪q.val, w⟫ = 0)
    (hneq : p ≠ q) (hθ : angularDist p q < Real.pi) :
    Real.sin (angularDist p q) * ‖differential (b / (a + b)) p.val q.val v w‖ ≤
      6 * (‖v - α • projectTangent p q.val‖ + ‖w - γ • projectTangent q p.val‖) := by
  have he1 : ⟪p.val, v - α • projectTangent p q.val⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right, projection_tangent, hv, mul_zero, sub_zero]
  have he2 : ⟪q.val, w - γ • projectTangent q p.val⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right, projection_tangent, hw, mul_zero, sub_zero]
  have heq : differential (b / (a + b)) p.val q.val v w =
      differential (b / (a + b)) p.val q.val
        (v - α • projectTangent p q.val) (w - γ • projectTangent q p.val) := by
    have hh := differential_add (b / (a + b)) p.val q.val
      (v - α • projectTangent p q.val) (w - γ • projectTangent q p.val)
      (α • projectTangent p q.val) (γ • projectTangent q p.val)
    rw [sub_add_cancel, sub_add_cancel,
      differential_pair_eq_zero a b ha hb p q α γ hbalance hneq hθ, add_zero] at hh
    exact hh
  rw [heq]
  exact sine_mul_norm_differential_le (b / (a + b))
    (div_nonneg hb.le (add_pos ha hb).le)
    ((div_le_one (add_pos ha hb)).mpr (by linarith only [ha]))
    p q _ _ he1 he2 hneq hθ

/-- A common relative tangent error cancels the sine loss in the barycenter
variation; the absolute errors only cost the reciprocal sine. -/
theorem norm_differential_le_error (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p q : Sphere d) (v w : Vector d) (α γ R E : ℝ)
    (hbalance : a * α = b * γ)
    (hv : ⟪p.val, v⟫ = 0) (hw : ⟪q.val, w⟫ = 0)
    (hneq : p ≠ q) (hθ : angularDist p q < Real.pi)
    (hve : ‖v - α • projectTangent p q.val‖ ≤ R * Real.sin (angularDist p q) + E)
    (hwe : ‖w - γ • projectTangent q p.val‖ ≤ R * Real.sin (angularDist p q) + E) :
    ‖differential (b / (a + b)) p.val q.val v w‖ ≤
      12 * (R + E / Real.sin (angularDist p q)) := by
  have hS : 0 < Real.sin (angularDist p q) := Real.sin_pos_of_pos_of_lt_pi
    (lt_of_le_of_ne (angularDist_nonneg p q) (fun hz => hneq ((angularDist_eq_zero_iff p q).mp hz.symm))) hθ
  have h := sine_mul_norm_differential_error_le a b ha hb p q v w α γ hbalance hv hw hneq hθ
  have hdiv := div_mul_cancel₀ E hS.ne'
  apply (mul_le_mul_iff_right₀ hS).mp
  nlinarith only [h, hve, hwe, hdiv]

end Metastability.BarycenterBounds
