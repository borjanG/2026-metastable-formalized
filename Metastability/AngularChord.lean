import Metastability.AngularGeometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Explicit comparison of the source angular distance with ambient distance. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Metastability.AngularChord
open Source AngularGeometry
variable {d : ℕ}

theorem norm_sub_eq_two_sin_half (x y : Sphere d) :
    ‖x.val - y.val‖ = 2 * Real.sin (angularDist x y / 2) := by
  have hn := norm_sub_sq_real x.val y.val
  rw [x.property, y.property, one_pow] at hn
  have hs := Real.sin_sq_eq_half_sub (angularDist x y / 2)
  rw [show 2 * (angularDist x y / 2) = angularDist x y by ring, cos_angularDist] at hs
  have hp : 0 ≤ Real.sin (angularDist x y / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (div_nonneg (angularDist_nonneg x y) (by norm_num))
      (by linarith only [angularDist_le_pi x y, Real.pi_pos])
  nlinarith only [hn, hs, hp, norm_nonneg (x.val - y.val)]

theorem angularDist_le_pi_half_norm (x y : Sphere d) :
    angularDist x y ≤ (Real.pi / 2) * ‖x.val - y.val‖ := by
  have hj := Real.mul_le_sin
    (show 0 ≤ angularDist x y / 2 from div_nonneg (angularDist_nonneg x y) (by norm_num))
    (show angularDist x y / 2 ≤ Real.pi / 2 from div_le_div_of_nonneg_right
      (angularDist_le_pi x y) (by norm_num))
  have hd : angularDist x y / Real.pi ≤ Real.sin (angularDist x y / 2) := by
    convert hj using 1
    ring
  have hm := (div_le_iff₀ Real.pi_pos).mp hd
  rw [norm_sub_eq_two_sin_half]
  nlinarith only [hm]

end Metastability.AngularChord
