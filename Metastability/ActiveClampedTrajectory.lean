import Metastability.ActiveTrajectory
import Metastability.ActiveLogCoordinate
import Metastability.AngularGeometry

/-! A globally regular stopped coordinate for the actual source trajectory. -/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Metastability.ActiveClampedTrajectory
open Source ActiveLogCoordinate
variable {n d : ℕ}

theorem correlation_lt_cos_iff (x y : Sphere d) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ⟪x.val, y.val⟫ < Real.cos θ ↔ θ < angularDist x y := by
  constructor
  · intro hr
    by_contra h
    exact (not_le.mpr hr) ((AngularGeometry.angularDist_le_iff_inner x y hθ0 hθπ).mp (le_of_not_gt h))
  · intro hθ
    by_contra h
    exact (not_le.mpr hθ) ((AngularGeometry.angularDist_le_iff_inner x y hθ0 hθπ).mpr (le_of_not_gt h))

theorem correlation_eq_cos_iff (x y : Sphere d) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ⟪x.val, y.val⟫ = Real.cos θ ↔ angularDist x y = θ := by
  constructor
  · intro h
    change Real.arccos ⟪x.val, y.val⟫ = θ
    rw [h, Real.arccos_cos hθ0 hθπ]
  · intro h
    rw [← AngularGeometry.cos_angularDist x y, h]

/-- The global clamp gives absolute continuity before a first hit has been
shown to exist, even if the untruncated coordinate is singular later on. -/
theorem absolutelyContinuous_clamped (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (i j : Fin n)
    {lo hi : ℝ} (hlo : -1 < lo) (hhi : hi < 1) (hlh : lo ≤ hi)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval
      (fun t => clampedLogHalfAngle lo hi ⟪(accelerated X shift clock t i).val,
        (accelerated X shift clock t j).val⟫) a b := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_clampedLogHalfAngle hlo hhi hlh
  have hlip := hK.comp_lipschitzOnWith
    (ActiveTrajectory.accelerated_correlation_lipschitz model β hβ X hX shift hshift clock hc i j)
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  apply hlip.mono
  rw [uIcc_of_le hab]
  exact fun _ ht => ha.trans ht.1

/-- The analytic clamp can cover the initial value and the entire stopped
active range. Its auxiliary endpoints need not be uniform in the trajectory. -/
theorem exists_clamp {r₀ target U : ℝ} (hr₀ : r₀ ∈ Ioo (-1 : ℝ) 1)
    (htarget : target ∈ Ioo (-1 : ℝ) 1) (hU : U < 2) (hUt : 1 - target < U) :
    ∃ lo hi : ℝ, -1 < lo ∧ hi < 1 ∧ lo < r₀ ∧ r₀ < hi ∧
      lo < 1 - U ∧ lo < target ∧ target < hi := by
  let lo := min ((r₀ - 1) / 2) (-U / 2)
  let hi := max ((r₀ + 1) / 2) ((target + 1) / 2)
  have hlow : -1 < lo := lt_min (by linarith only [hr₀.1]) (by linarith only [hU])
  have hhigh : hi < 1 := max_lt (by linarith only [hr₀.2]) (by linarith only [htarget.2])
  have hlr : lo < r₀ := (min_le_left _ _).trans_lt (by linarith only [hr₀.1])
  have hrh : r₀ < hi := lt_of_lt_of_le (by linarith only [hr₀.2] : r₀ < (r₀ + 1) / 2)
    (le_max_left _ _)
  have hlU : lo < 1 - U := (min_le_right _ _).trans_lt (by linarith only [hU])
  have hlt : lo < target := hlU.trans (by linarith only [hUt])
  have hth : target < hi := lt_of_lt_of_le (by linarith only [htarget.2] : target < (target + 1) / 2)
    (le_max_right _ _)
  exact ⟨lo, hi, hlow, hhigh, hlr, hrh, hlU, hlt, hth⟩

end Metastability.ActiveClampedTrajectory
