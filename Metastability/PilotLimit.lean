import Metastability.PilotCutoff

/-!
# Assembling the two-particle energy limit across the cutoff

These are conditional analytic helpers. The final dynamical application must
prove the profile identity up to the cutoff, energy monotonicity, and the energy
upper bound from the actual particle equations and constructed clock.
The continuation after the cutoff is controlled by monotonicity and the energy
at the cutoff; it is not identified with the uncut auxiliary profile.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace Metastability.PilotLimit

open PilotAsymptotics PilotCutoff

/-- Any energy family agreeing with the profile until the cutoff has the left
plateau limit on compact sets strictly before the jump. -/
theorem tendstoUniformlyOn_before (a : ℝ) (ha : 0 < a) (E : ℝ → ℝ → ℝ)
    (hprofile : ∀ᶠ β : ℝ in atTop, ∀ t ∈ Icc 0 (cutoffTime a β),
      E β t = analyticEnergy a β t)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ico 0 (1 / 2)) :
    TendstoUniformlyOn E (fun _ => 1 / 2) atTop K := by
  rcases eq_empty_or_nonempty K with h | hne
  · subst K
    exact tendstoUniformlyOn_empty
  have hu := hKsub (hK.sSup_mem hne)
  have hcut : ∀ᶠ β : ℝ in atTop, sSup K < cutoffTime a β :=
    (tendsto_cutoffTime a).eventually (lt_mem_nhds hu.2)
  have hE := tendstoUniformlyOn_analyticEnergy_before a ha hK hKsub
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hprofile, hcut, Metric.tendstoUniformlyOn_iff.mp hE ε hε]
    with β hp hc he
  intro t ht
  rw [hp t ⟨(hKsub ht).1, (le_csSup hK.bddAbove ht).trans hc.le⟩]
  exact he t ht

/-- Monotonicity after the exact cutoff gives the right plateau limit, without
using the uncut profile for later times. -/
theorem tendstoUniformlyOn_after (a : ℝ) (ha : 0 < a) (E : ℝ → ℝ → ℝ)
    (hprofile : ∀ᶠ β : ℝ in atTop, ∀ t ∈ Icc 0 (cutoffTime a β),
      E β t = analyticEnergy a β t)
    (hmono : ∀ᶠ β : ℝ in atTop, MonotoneOn (E β) (Ici 0))
    (hupper : ∀ᶠ β : ℝ in atTop, ∀ t ∈ Ici 0, E β t ≤ 1)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioi (1 / 2)) :
    TendstoUniformlyOn E (fun _ => 1) atTop K := by
  rcases eq_empty_or_nonempty K with h | hne
  · subst K
    exact tendstoUniformlyOn_empty
  have hl := hKsub (hK.sInf_mem hne)
  have hcut : ∀ᶠ β : ℝ in atTop, cutoffTime a β < sInf K :=
    (tendsto_cutoffTime a).eventually (gt_mem_nhds hl)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hE := Metric.tendsto_nhds.mp (tendsto_analyticEnergy_cutoffTime a ha) ε hε
  filter_upwards [hprofile, hmono, hupper, hcut, eventually_cutoffTime_pos a, hE]
    with β hp hm hu hc hpos he
  intro t ht
  have ht0 : 0 ≤ t := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) (hKsub ht).le
  have hct : cutoffTime a β ≤ t := hc.le.trans (csInf_le hK.bddBelow ht)
  have hlo := hm hpos.le ht0 hct
  rw [hp _ ⟨hpos.le, le_rfl⟩] at hlo
  have hup := hu t ht0
  rw [Real.dist_eq] at he
  rw [Real.dist_eq, abs_sub_comm]
  rw [abs_of_nonpos (sub_nonpos.mpr hup)]
  exact lt_of_le_of_lt (by linarith only [hlo, neg_le_abs (analyticEnergy a β (cutoffTime a β) - 1)]) he

/-- Uniform energy staircase convergence away from the unique two-particle jump.
All three input properties are explicit internal proof obligations, not source
hypotheses of the final metastability theorem. -/
theorem tendstoUniformlyOn_staircase (a : ℝ) (ha : 0 < a) (E : ℝ → ℝ → ℝ)
    (hprofile : ∀ᶠ β : ℝ in atTop, ∀ t ∈ Icc 0 (cutoffTime a β),
      E β t = analyticEnergy a β t)
    (hmono : ∀ᶠ β : ℝ in atTop, MonotoneOn (E β) (Ici 0))
    (hupper : ∀ᶠ β : ℝ in atTop, ∀ t ∈ Ici 0, E β t ≤ 1)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ici 0) (hjump : (1 / 2 : ℝ) ∉ K) :
    TendstoUniformlyOn E (fun t => if t < 1 / 2 then 1 / 2 else 1) atTop K := by
  have hleftsub : K ∩ Iic (1 / 2 : ℝ) ⊆ Ico 0 (1 / 2) := by
    intro t ht
    refine ⟨hKsub ht.1, lt_of_le_of_ne ht.2 ?_⟩
    intro he
    exact hjump (he ▸ ht.1)
  have hrightsub : K ∩ Ici (1 / 2 : ℝ) ⊆ Ioi (1 / 2) := by
    intro t ht
    change (1 / 2 : ℝ) < t
    apply lt_of_le_of_ne (show (1 / 2 : ℝ) ≤ t from ht.2)
    intro he
    exact hjump (he.symm ▸ ht.1)
  have hleft := tendstoUniformlyOn_before a ha E hprofile
    (hK.inter_right isClosed_Iic) hleftsub
  have hright := tendstoUniformlyOn_after a ha E hprofile hmono hupper
    (hK.inter_right isClosed_Ici) hrightsub
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hleft ε hε,
    Metric.tendstoUniformlyOn_iff.mp hright ε hε] with β hl hr
  intro t ht
  by_cases hj : t < 1 / 2
  · rw [if_pos hj]
    exact hl t ⟨ht, hj.le⟩
  · rw [if_neg hj]
    exact hr t ⟨ht, le_of_not_gt hj⟩

end Metastability.PilotLimit
