import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# The active logarithmic half-angle coordinate

On the correlation interval `(-1,1)` this is literally
`log (tan (arccos q / 2))`. A clamped extension is provided only as an analytic
tool for stopped arguments; its agreement on the stated interval is proved.
-/

noncomputable section
open Set

namespace Metastability.ActiveLogCoordinate

def logHalfAngle (q : ℝ) : ℝ := (Real.log (1 - q) - Real.log (1 + q)) / 2

theorem hasDerivAt_logHalfAngle {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt logHalfAngle (-(1 / (1 - q ^ 2))) q := by
  have hn : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq.2)
  have hp : 1 + q ≠ 0 := ne_of_gt (by linarith only [hq.1])
  have hd := ((((hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q)).log hn).sub
    (((hasDerivAt_const q (1 : ℝ)).add (hasDerivAt_id q)).log hp)).div_const 2
  convert hd using 1
  change -(1 / (1 - q ^ 2)) = ((0 - 1) / (1 - q) - (0 + 1) / (1 + q)) / 2
  have hsq : 1 - q ^ 2 ≠ 0 := by
    rw [show 1 - q ^ 2 = (1 - q) * (1 + q) by ring]
    exact mul_ne_zero hn hp
  field_simp
  ring

theorem hasDerivAt_logHalfAngle_comp {ρ : ℝ → ℝ} {t v : ℝ}
    (hρ : ρ t ∈ Ioo (-1 : ℝ) 1) (hd : HasDerivAt ρ v t) :
    HasDerivAt (fun u => logHalfAngle (ρ u)) (-v / (1 - ρ t ^ 2)) t := by
  convert (hasDerivAt_logHalfAngle hρ).comp t hd using 1
  ring

theorem logHalfAngle_eq_log_tan_arccos {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    logHalfAngle q = Real.log (Real.tan (Real.arccos q / 2)) := by
  have hn : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq.2)
  have hp : 1 + q ≠ 0 := ne_of_gt (by linarith only [hq.1])
  have hc : Real.cos (Real.arccos q) = q := Real.cos_arccos hq.1.le hq.2.le
  have hrep := Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq
    (Real.arccos q) (by rw [hc]; linarith only [hq.1])
  rw [hc] at hrep
  have ht : 1 + Real.tan (Real.arccos q / 2) ^ 2 ≠ 0 := by positivity
  have hmul := (eq_div_iff ht).mp hrep
  have heq : (1 - q) / (1 + q) = Real.tan (Real.arccos q / 2) ^ 2 := by
    apply (div_eq_iff hp).mpr
    nlinarith only [hmul]
  unfold logHalfAngle
  rw [← Real.log_div hn hp, heq, Real.log_pow]
  norm_num

theorem continuousOn_logHalfAngle : ContinuousOn logHalfAngle (Ioo (-1 : ℝ) 1) :=
  fun _ hq => (hasDerivAt_logHalfAngle hq).continuousAt.continuousWithinAt

/-- A finite Lipschitz constant exists on any closed correlation interval
strictly inside `(-1,1)`. The interval endpoints may depend on beta. -/
theorem exists_lipschitzOnWith_logHalfAngle {lo hi : ℝ}
    (hlo : -1 < lo) (hhi : hi < 1) :
    ∃ K : NNReal, LipschitzOnWith K logHalfAngle (Icc lo hi) := by
  have hc : ContDiffOn ℝ 1 logHalfAngle (Icc lo hi) := by
    apply ContDiffOn.div_const
    apply ContDiffOn.sub
    · apply ContDiffOn.log (contDiffOn_const.sub contDiffOn_id)
      intro x hx
      exact ne_of_gt (sub_pos.mpr (hx.2.trans_lt hhi))
    · apply ContDiffOn.log (contDiffOn_const.add contDiffOn_id)
      intro x hx
      change 1 + x ≠ 0
      exact ne_of_gt (by linarith only [hlo, hx.1])
  exact hc.exists_lipschitzOnWith (by norm_num) (convex_Icc lo hi) isCompact_Icc

def clampedLogHalfAngle (lo hi q : ℝ) : ℝ := logHalfAngle (max lo (min q hi))

theorem clampedLogHalfAngle_eq {lo hi q : ℝ} (hq : q ∈ Icc lo hi) :
    clampedLogHalfAngle lo hi q = logHalfAngle q := by
  simp only [clampedLogHalfAngle, min_eq_left hq.2, max_eq_right hq.1]

/-- The clamp has a global Lipschitz bound and therefore can be composed with
an accelerated Lipschitz trajectory before locating its first hitting time. -/
theorem exists_lipschitzWith_clampedLogHalfAngle {lo hi : ℝ}
    (hlo : -1 < lo) (hhi : hi < 1) (hlh : lo ≤ hi) :
    ∃ K : NNReal, LipschitzWith K (clampedLogHalfAngle lo hi) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_logHalfAngle hlo hhi
  have hclamp : LipschitzWith 1 (fun q : ℝ => max lo (min q hi)) := by
    exact (LipschitzWith.id.min_const hi).const_max lo
  have hm : MapsTo (fun q : ℝ => max lo (min q hi)) univ (Icc lo hi) := by
    intro q _
    exact ⟨le_max_left _ _, max_le hlh (min_le_right _ _)⟩
  have hcomp := hK.comp hclamp.lipschitzOnWith hm
  exact ⟨K, by simpa only [mul_one, lipschitzOnWith_univ] using hcomp⟩

theorem strictAntiOn_logHalfAngle : StrictAntiOn logHalfAngle (Ioo (-1 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (-1 : ℝ) 1) continuousOn_logHalfAngle
  intro q hq
  have hq' : q ∈ Ioo (-1 : ℝ) 1 := interior_subset hq
  rw [(hasDerivAt_logHalfAngle hq').deriv]
  have hp : 0 < 1 - q ^ 2 := by nlinarith only [hq'.1, hq'.2]
  exact neg_neg_of_pos (div_pos (by norm_num) hp)

theorem hasDerivAt_clampedLogHalfAngle {lo hi q : ℝ}
    (hlo : -1 < lo) (hhi : hi < 1) (hq : q ∈ Ioo lo hi) :
    HasDerivAt (clampedLogHalfAngle lo hi) (-(1 / (1 - q ^ 2))) q := by
  apply (hasDerivAt_logHalfAngle ⟨hlo.trans hq.1, hq.2.trans hhi⟩).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with x hx
  exact clampedLogHalfAngle_eq ⟨hx.1.le, hx.2.le⟩

theorem clampedLogHalfAngle_gt_iff {lo hi target q : ℝ}
    (hlo : -1 < lo) (hhi : hi < 1) (ht : target ∈ Ioo lo hi) :
    logHalfAngle target < clampedLogHalfAngle lo hi q ↔ q < target := by
  have htc : target ∈ Ioo (-1 : ℝ) 1 := ⟨hlo.trans ht.1, ht.2.trans hhi⟩
  have hqc : max lo (min q hi) ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hlo.trans_le (le_max_left _ _), (max_le (ht.1.le.trans ht.2.le) (min_le_right _ _)).trans_lt hhi⟩
  constructor
  · intro h
    by_contra hn
    have hle : target ≤ max lo (min q hi) :=
      (le_min (le_of_not_gt hn) ht.2.le).trans (le_max_right _ _)
    exact (not_lt_of_ge (strictAntiOn_logHalfAngle.antitoneOn htc hqc hle)) h
  · intro hq
    exact strictAntiOn_logHalfAngle hqc htc
      (max_lt ht.1 ((min_le_left _ _).trans_lt hq))

theorem clampedLogHalfAngle_eq_iff {lo hi target q : ℝ}
    (hlo : -1 < lo) (hhi : hi < 1) (ht : target ∈ Ioo lo hi) :
    clampedLogHalfAngle lo hi q = logHalfAngle target ↔ q = target := by
  constructor
  · intro heq
    rcases lt_trichotomy q target with hq | he | hq
    · exact False.elim ((ne_of_gt ((clampedLogHalfAngle_gt_iff hlo hhi ht).mpr hq)) heq)
    · exact he
    · have htc : target ∈ Ioo (-1 : ℝ) 1 := ⟨hlo.trans ht.1, ht.2.trans hhi⟩
      have hqc : max lo (min q hi) ∈ Ioo (-1 : ℝ) 1 :=
        ⟨hlo.trans_le (le_max_left _ _), (max_le (ht.1.le.trans ht.2.le) (min_le_right _ _)).trans_lt hhi⟩
      have h := strictAntiOn_logHalfAngle htc hqc
        ((lt_min hq ht.2).trans_le (le_max_right _ _))
      exact False.elim (h.ne heq)
  · rintro rfl
    exact clampedLogHalfAngle_eq ⟨ht.1.le, ht.2.le⟩

end Metastability.ActiveLogCoordinate
