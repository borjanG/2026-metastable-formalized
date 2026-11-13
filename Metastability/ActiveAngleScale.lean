import Metastability.ContractionScale

/-! Sharp angular estimates on the source mesoscopic scale. -/
noncomputable section
open scoped RealInnerProductSpace

namespace Metastability.ActiveAngleScale
open Source AngularGeometry

/-- A quantitative small-angle lower bound strong enough for the SA error rate. -/
theorem two_fifths_sq_le_deficit {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (2 / 5 : ℝ) * θ ^ 2 ≤ 1 - Real.cos θ := by
  rcases hθ0.eq_or_lt with hz | hp
  · rw [← hz]
    norm_num
  have hh : 0 < θ / 2 := by linarith only [hp]
  have hsin := (Real.sin_gt_sub_cube hh (by linarith only [hθ1] : θ / 2 ≤ 1)).le
  have hs : θ ^ 2 ≤ 1 := by nlinarith only [hθ0, hθ1]
  have hcube := mul_le_mul_of_nonneg_right hs hθ0
  have hlo : 15 * θ / 32 ≤ Real.sin (θ / 2) := by nlinarith only [hsin, hcube]
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 15 * θ / 32) hlo 2
  have hhalf := Real.sin_sq_eq_half_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hhalf
  nlinarith only [hsq, hhalf, sq_nonneg θ]

theorem mesoscopic_deficit_lower {d : ℕ} (β : ℝ) (hβ : 1 < β)
    (hsmall : Real.sqrt (Real.log β / β) ≤ 1) (x y : Sphere d)
    (hangle : Real.sqrt (Real.log β / β) ≤ angularDist x y) :
    (2 / 5 : ℝ) * (Real.log β / β) ≤ 1 - ⟪x.val, y.val⟫ := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlog : 0 < Real.log β := Real.log_pos hβ
  have hq := two_fifths_sq_le_deficit (Real.sqrt_nonneg _) hsmall
  rw [Real.sq_sqrt (div_pos hlog hβ0).le] at hq
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (Real.sqrt_nonneg _)
    (angularDist_le_pi x y) hangle
  rw [cos_angularDist] at hcos
  linarith only [hq, hcos]

/-- The active cross kernel is smaller than beta to the minus one third. -/
theorem kernel_le_third_power {d : ℕ} (β : ℝ) (hβ : 1 < β)
    (hsmall : Real.sqrt (Real.log β / β) ≤ 1) (x y : Sphere d)
    (hangle : Real.sqrt (Real.log β / β) ≤ angularDist x y) :
    Real.exp (β * (⟪x.val, y.val⟫ - 1)) ≤ β ^ (-(1 : ℝ) / 3) := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hq := mesoscopic_deficit_lower β hβ hsmall x y hangle
  have hmul := mul_le_mul_of_nonneg_left hq hβ0.le
  have he : β * (⟪x.val, y.val⟫ - 1) ≤ -(2 / 5 : ℝ) * Real.log β := by
    have hc : β * ((2 / 5 : ℝ) * (Real.log β / β)) = (2 / 5 : ℝ) * Real.log β := by
      field_simp
    rw [hc] at hmul
    linarith only [hmul]
  calc
    _ ≤ Real.exp (-(2 / 5 : ℝ) * Real.log β) := Real.exp_le_exp.mpr he
    _ = β ^ (-(2 / 5 : ℝ)) := by rw [Real.rpow_def_of_pos hβ0]; congr 1; ring
    _ ≤ β ^ (-(1 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_exponent_le hβ.le (by norm_num)

/-- The fixed upper barrier keeps the active angle away from pi, so the
mesoscopic lower angle yields a uniform lower bound on its sine squared. -/
theorem sine_sq_lower {d : ℕ} (β U : ℝ) (hβ : 1 < β) (hU : U < 2)
    (hsmall : Real.sqrt (Real.log β / β) ≤ 1) (x y : Sphere d)
    (hangle : Real.sqrt (Real.log β / β) ≤ angularDist x y)
    (hupper : 1 - ⟪x.val, y.val⟫ ≤ U) :
    ((2 / 5 : ℝ) * (2 - U)) * (Real.log β / β) ≤ 1 - ⟪x.val, y.val⟫ ^ 2 := by
  have hq := mesoscopic_deficit_lower β hβ hsmall x y hangle
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlog := Real.log_pos hβ
  have hp : 0 ≤ (2 / 5 : ℝ) * (Real.log β / β) := by positivity
  have hother : 2 - U ≤ 1 + ⟪x.val, y.val⟫ := by linarith only [hupper]
  have hprod := mul_le_mul hq hother (by linarith only [hU] : 0 ≤ 2 - U)
    (sub_nonneg.mpr (ModelBounds.inner_bounds x y).2)
  nlinarith only [hprod]

end Metastability.ActiveAngleScale
