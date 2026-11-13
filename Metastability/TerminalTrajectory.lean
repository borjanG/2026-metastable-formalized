import Metastability.SourceTerminalEstimates
import Metastability.ActiveBarrier
import Metastability.ActiveTimingScales

/-! Integration and no-upward-exit for actual accelerated correlations. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology RealInnerProductSpace
namespace Metastability.TerminalTrajectory
open Source ActiveCoefficients ActiveVelocity ActiveScales ActiveLogCoordinate ActiveTimingScales
variable {n d : ℕ}

theorem cos_mem_Ioo {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    Real.cos θ ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · simpa only [Real.cos_pi] using Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
  · simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hθπ.le hθ0

theorem angle_le_of_cos_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (x y : Sphere d) (h : Real.cos θ ≤ ⟪x.val, y.val⟫) : angularDist x y ≤ θ := by
  have hh := Real.arccos_le_arccos h
  rwa [Real.arccos_cos hθ0 hθπ] at hh

/-- Actual accelerated correlations cannot cross downward through the
mesoscopic correlation while the original velocity is positive on the doubled
angular band. This is an internal integration helper; its pointwise premise
is discharged by the source terminal estimates. -/
theorem no_upward_exit (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ) (hc : ClockRelation β X shift clock)
    (i j : Fin n) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hsmall : 2 * mesoscopicScale β ≤ 1)
    (hstart : angularDist (accelerated X shift clock a i) (accelerated X shift clock a j) = mesoscopicScale β)
    (hpositive : ∀ t ∈ Ioo a b,
      angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ≤ 2 * mesoscopicScale β →
      0 < -PairDeficit.velocity model β (accelerated X shift clock t) i j) :
    ∀ t ∈ Icc a b,
      angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ≤ mesoscopicScale β := by
  let ρ := fun t => ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫
  have hmpos := mesoscopicScale_pos hβ
  have h2π : 2 * mesoscopicScale β ≤ Real.pi := hsmall.trans (by linarith only [Real.two_le_pi])
  have hmπ : mesoscopicScale β ≤ Real.pi := by linarith only [h2π, hmpos]
  have hac := ActiveTrajectory.accelerated_correlation_absolutelyContinuous model β hβ X hX
    shift hshift clock hc i j a b ha hab
  have hstartρ : ρ a = Real.cos (mesoscopicScale β) := by
    dsimp only [ρ]
    rw [← AngularGeometry.cos_angularDist, hstart]
  have hAE := (ae_restrict_iff' measurableSet_Ici).mp
    (ActiveTrajectory.ae_accelerated_correlation_hasDerivAt model β X hX shift hshift clock hc i j)
  have hbar := ActiveBarrier.no_downcross_of_ae_deriv_nonneg_on_band hab hac
    (Real.cos_lt_cos_of_nonneg_of_le_pi hmpos.le h2π (by linarith only [hmpos])) hstartρ (by
      filter_upwards [hAE] with t ht htab hband
      have ht0 : 0 ≤ t := ha.trans htab.1.le
      have hangle := angle_le_of_cos_le (by positivity : 0 ≤ 2 * mesoscopicScale β) h2π
        (accelerated X shift clock t i) (accelerated X shift clock t j) hband.1
      have hv := hpositive t htab hangle
      have hclock : 0 < clockFactor β (accelerated X shift clock t) :=
        (lt_min zero_lt_one (Real.log_pos hβ)).trans_le (GeneralClock.clockFactor_bounds β hβ _).1
      rw [(ht ht0).deriv]
      exact (mul_pos hv hclock).le)
  intro t ht
  exact angle_le_of_cos_le hmpos.le hmπ _ _ (hbar t ht)

/-- No interval can remain uncompleted longer than the logarithmic budget
when supplied with the already-derived source pointwise estimates. -/
theorem impossible_terminal_interval (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ) (hc : ClockRelation β X shift clock)
    (i j : Fin n) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hsmall : 2 * mesoscopicScale β ≤ 1)
    (hstart : angularDist (accelerated X shift clock a i) (accelerated X shift clock a j) = mesoscopicScale β)
    (hpoint : ∀ t ∈ Icc a b,
      angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ≤ 2 * mesoscopicScale β →
      clockCutoff β / 2 < angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ∧
      0 < -PairDeficit.velocity model β (accelerated X shift clock t) i j ∧
      (angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ≤ mesoscopicScale β →
        Real.log β / (4 * n) * sineSquare (accelerated X shift clock t) i j ≤
          (-PairDeficit.velocity model β (accelerated X shift clock t) i j) *
            clockFactor β (accelerated X shift clock t)))
    (hbudget : angleLog (mesoscopicScale β) - angleLog (clockCutoff β / 2) ≤
      (Real.log β / (4 * n)) * (b - a)) : False := by
  let Y := accelerated X shift clock
  let ρ := fun t => ⟪(Y t i).val, (Y t j).val⟫
  let f := fun t => logHalfAngle (ρ t)
  have hmpos := mesoscopicScale_pos hβ
  have hmπ : mesoscopicScale β < Real.pi := by linarith only [hsmall, hmpos, Real.two_le_pi]
  have hconf := no_upward_exit model β hβ X hX shift hshift clock hc i j a b ha hab hsmall hstart
    (fun t ht hangle => (hpoint t ⟨ht.1.le, ht.2.le⟩ hangle).2.1)
  have hlow : ∀ t ∈ Icc a b, clockCutoff β / 2 < angularDist (Y t i) (Y t j) := by
    intro t ht
    exact (hpoint t ht ((hconf t ht).trans (by linarith only [hmpos]))).1
  have hcut0 : 0 < clockCutoff β / 2 := div_pos (clockCutoff_pos hβ) (by norm_num)
  have hcutπ' : clockCutoff β / 2 < Real.pi := by
    exact (hlow a ⟨le_rfl, hab⟩).trans ((hconf a ⟨le_rfl, hab⟩).trans_lt hmπ)
  have hcoslo := cos_mem_Ioo hmpos hmπ
  have hcoshi := cos_mem_Ioo hcut0 hcutπ'
  have hrange : ∀ t ∈ Icc a b, ρ t ∈ Icc (Real.cos (mesoscopicScale β)) (Real.cos (clockCutoff β / 2)) := by
    intro t ht
    constructor
    · have hh := Real.cos_le_cos_of_nonneg_of_le_pi
        (AngularGeometry.angularDist_nonneg (Y t i) (Y t j)) hmπ.le (hconf t ht)
      simpa only [AngularGeometry.cos_angularDist] using hh
    · have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hcut0.le
        (AngularGeometry.angularDist_le_pi (Y t i) (Y t j)) (hlow t ht)
      exact (by simpa only [AngularGeometry.cos_angularDist] using hh : ρ t < Real.cos (clockCutoff β / 2)).le
  have hrange' : ∀ t ∈ Icc a b, ρ t ∈ Ioo (-1 : ℝ) 1 :=
    fun t ht => ⟨hcoslo.1.trans_le (hrange t ht).1, (hrange t ht).2.trans_lt hcoshi.2⟩
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_logHalfAngle hcoslo.1 hcoshi.2
  have hρlip := (ActiveTrajectory.accelerated_correlation_lipschitz model β hβ X hX
    shift hshift clock hc i j).mono (show Icc a b ⊆ Ici (0 : ℝ) from fun t ht => ha.trans ht.1)
  have hflip := hK.comp hρlip hrange
  have hfac : AbsolutelyContinuousOnInterval f a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab] using hflip
  have hAE := (ae_restrict_iff' measurableSet_Ici).mp
    (ActiveTrajectory.ae_accelerated_correlation_hasDerivAt model β X hX shift hshift clock hc i j)
  have hdec := ActiveTiming.sub_le_of_ae_deriv_le hab hfac (upper := -(Real.log β / (4 * n))) (by
    filter_upwards [hAE] with t ht htab
    have htab' : t ∈ Icc a b := ⟨htab.1.le, htab.2.le⟩
    have hangle := hconf t htab'
    have hest := (hpoint t htab' (hangle.trans (by linarith only [hmpos]))).2.2 hangle
    have hd := hasDerivAt_logHalfAngle_comp (hrange' t htab') (ht (ha.trans htab.1.le))
    change HasDerivAt f _ t at hd
    rw [hd.deriv]
    have hspos : 0 < 1 - ρ t ^ 2 := by
      have hh := hrange' t htab'
      nlinarith only [hh.1, hh.2]
    apply (div_le_iff₀ hspos).mpr
    change Real.log β / (4 * n) * (1 - ρ t ^ 2) ≤ _ at hest
    linarith only [hest])
  have hfa : f a = angleLog (mesoscopicScale β) := by
    dsimp only [f, ρ, Y]
    rw [← AngularGeometry.cos_angularDist, hstart]
    exact (angleLog_eq_logHalfAngle_cos ⟨hmpos, hmπ⟩).symm
  have hfb : angleLog (clockCutoff β / 2) < f b := by
    rw [angleLog_eq_logHalfAngle_cos ⟨hcut0, hcutπ'⟩]
    apply strictAntiOn_logHalfAngle (hrange' b ⟨hab, le_rfl⟩) hcoshi
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hcut0.le
      (AngularGeometry.angularDist_le_pi (Y b i) (Y b j)) (hlow b ⟨hab, le_rfl⟩)
    simpa only [AngularGeometry.cos_angularDist] using hh
  rw [hfa] at hdec
  nlinarith only [hdec, hfb, hbudget]

end Metastability.TerminalTrajectory
