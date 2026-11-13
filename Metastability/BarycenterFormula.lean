import Metastability.GeodesicBarycenter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# An analytic formula for the literal weighted geodesic point

The ambient formula is a calculus device. On every non-antipodal unit pair it
is proved equal to the manuscript's interpolation, including coincident points.
-/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.BarycenterFormula
open Source AngularGeometry
variable {d : ℕ}

def vector (s : ℝ) (p q : Vector d) : Vector d :=
  let ρ := ⟪p, q⟫
  let θ := Real.arccos ρ
  Real.cos (s * θ) • p + (Real.sin (s * θ) / Real.sin θ) • (q - ρ • p)

theorem vector_eq_source (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p q : Sphere d) (hθ : angularDist p q < Real.pi) :
    vector (b / (a + b)) p.val q.val = geodesicBarycenter a b ha hb p q hθ := by
  by_cases he : p = q
  · subst q
    simp only [vector, real_inner_self_eq_norm_sq, p.property, one_pow, Real.arccos_one,
      mul_zero, Real.cos_zero, one_smul, Real.sin_zero, div_zero, zero_smul, add_zero,
      geodesicBarycenter, if_true]
  · have hid := GeodesicBarycenter.sine_interpolation_coordinate
      (GeodesicBarycenter.weighted_angles_sum a b (angularDist p q) ha hb)
      (GeodesicBarycenter.sin_angularDist_ne_zero he hθ)
    rw [cos_angularDist] at hid
    change Real.cos (b / (a + b) * angularDist p q) • p.val +
      (Real.sin (b / (a + b) * angularDist p q) / Real.sin (angularDist p q)) •
        (q.val - ⟪p.val, q.val⟫ • p.val) = _
    rw [geodesicBarycenter, if_neg he, ← hid]
    module

theorem vector_eq_point (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p q : Sphere d) (hθ : angularDist p q < Real.pi) :
    vector (b / (a + b)) p.val q.val =
      (GeodesicBarycenter.point a b ha hb p q hθ).val :=
  vector_eq_source a b ha hb p q hθ

def correlationVelocity (p q v w : Vector d) : ℝ := ⟪v, q⟫ + ⟪p, w⟫

def angleVelocity (p q v w : Vector d) : ℝ :=
  -correlationVelocity p q v w / Real.sin (Real.arccos ⟪p, q⟫)

def ratioDerivative (s θ : ℝ) : ℝ :=
  (s * Real.cos (s * θ) * Real.sin θ - Real.sin (s * θ) * Real.cos θ) / Real.sin θ ^ 2

def differential (s : ℝ) (p q v w : Vector d) : Vector d :=
  let ρ := ⟪p, q⟫
  let θ := Real.arccos ρ
  let θ' := angleVelocity p q v w
  (-(Real.sin (s * θ) * (s * θ'))) • p + Real.cos (s * θ) • v +
    (ratioDerivative s θ * θ') • (q - ρ • p) +
    (Real.sin (s * θ) / Real.sin θ) •
      (w - (correlationVelocity p q v w • p + ρ • v))

theorem hasDerivAt_ratio (s θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.sin (s * t) / Real.sin t) (ratioDerivative s θ) θ := by
  convert (((hasDerivAt_id θ).const_mul s).sin.div (Real.hasDerivAt_sin θ) hθ) using 1
  simp only [ratioDerivative, mul_one, id_eq]
  ring

/-- The off-diagonal differential is obtained by the ordinary chain rule. -/
theorem hasDerivAt_vector (s : ℝ) (p q : ℝ → Vector d) (v w : Vector d) (t : ℝ)
    (hp : HasDerivAt p v t) (hq : HasDerivAt q w t)
    (hρlo : -1 < ⟪p t, q t⟫) (hρhi : ⟪p t, q t⟫ < 1) :
    HasDerivAt (fun u => vector s (p u) (q u)) (differential s (p t) (q t) v w) t := by
  have hρ := hp.inner ℝ hq
  have hθ : HasDerivAt (fun u => Real.arccos ⟪p u, q u⟫)
      (angleVelocity (p t) (q t) v w) t := by
    have hd := (Real.hasDerivAt_arccos (ne_of_gt hρlo) (ne_of_lt hρhi)).comp t hρ
    convert hd using 1
    rw [angleVelocity, correlationVelocity, Real.sin_arccos]
    ring
  have hsin : Real.sin (Real.arccos ⟪p t, q t⟫) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr hρhi) (Real.arccos_lt_pi.mpr hρlo)).ne'
  have hratio := (hasDerivAt_ratio s _ hsin).comp t hθ
  have hcos := (hθ.const_mul s).cos
  have horth := hq.sub (hρ.smul hp)
  convert (hcos.smul hp).add (hratio.smul horth) using 1
  change differential s (p t) (q t) v w =
    Real.cos (s * Real.arccos ⟪p t, q t⟫) • v +
      (-Real.sin (s * Real.arccos ⟪p t, q t⟫) * (s * angleVelocity (p t) (q t) v w)) • p t +
      ((Real.sin (s * Real.arccos ⟪p t, q t⟫) / Real.sin (Real.arccos ⟪p t, q t⟫)) •
        (w - (⟪p t, q t⟫ • v + (⟪p t, w⟫ + ⟪v, q t⟫) • p t)) +
      (ratioDerivative s (Real.arccos ⟪p t, q t⟫) * angleVelocity (p t) (q t) v w) •
        (q t - ⟪p t, q t⟫ • p t))
  dsimp only [differential, correlationVelocity]
  module

/-- Every derivative of a sphere-valued curve is tangent at its base point. -/
theorem derivative_tangent (p : ℝ → Sphere d) (v : Vector d) (t : ℝ)
    (hp : HasDerivAt (fun u => (p u).val) v t) : ⟪(p t).val, v⟫ = 0 := by
  have hh := hp.inner ℝ hp
  have heq : (fun u => ⟪(p u).val, (p u).val⟫) = fun _ : ℝ => (1 : ℝ) := by
    funext u
    rw [real_inner_self_eq_norm_sq, (p u).property, one_pow]
  rw [heq] at hh
  have hzero := hh.unique (hasDerivAt_const t (1 : ℝ))
  have hc : ⟪v, (p t).val⟫ = ⟪(p t).val, v⟫ := real_inner_comm _ _
  rw [hc] at hzero
  linarith only [hzero]

theorem differential_add (s : ℝ) (p q v₁ w₁ v₂ w₂ : Vector d) :
    differential s p q (v₁ + v₂) (w₁ + w₂) =
      differential s p q v₁ w₁ + differential s p q v₂ w₂ := by
  simp only [differential, angleVelocity, correlationVelocity, inner_add_left, inner_add_right]
  module

theorem differential_smul (s r : ℝ) (p q v w : Vector d) :
    differential s p q (r • v) (r • w) = r • differential s p q v w := by
  simp only [differential, angleVelocity, correlationVelocity, real_inner_smul_left, inner_smul_right]
  module

/-- Unit tangent projections have exactly the angular sine as their norm. -/
theorem norm_projectTangent (p q : Sphere d) :
    ‖projectTangent p q.val‖ = Real.sin (angularDist p q) := by
  have hs : 0 ≤ Real.sin (angularDist p q) := Real.sin_nonneg_of_nonneg_of_le_pi
    (angularDist_nonneg p q) (angularDist_le_pi p q)
  have hid := Real.sin_sq_add_cos_sq (angularDist p q)
  rw [cos_angularDist] at hid
  have hn : ‖projectTangent p q.val‖ ^ 2 = 1 - ⟪p.val, q.val⟫ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, projectTangent, inner_sub_left, inner_sub_right,
      inner_sub_right, real_inner_smul_left, inner_smul_right, real_inner_smul_left,
      inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      p.property, q.property, one_pow, real_inner_comm q.val p.val]
    ring
  nlinarith only [hn, hid, hs, norm_nonneg (projectTangent p q.val)]

theorem projection_tangent (p q : Sphere d) : ⟪p.val, projectTangent p q.val⟫ = 0 := by
  simp only [projectTangent, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, p.property, one_pow, mul_one, sub_self]

end Metastability.BarycenterFormula
