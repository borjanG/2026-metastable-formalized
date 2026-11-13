import Metastability.ActiveTrajectory

/-! Transfer between closed or half-open plateau intervals and their exact
original-time images, using the source inverse-clock identities. -/

noncomputable section
open Set

namespace Metastability.PlateauClockTransfer
open Source
variable {n d : ℕ}

theorem exists_time_Icc {β shift : ℝ} {X : ℝ → Configuration n d}
    {clock : ℝ → ℝ} (hc : ClockRelation β X shift clock)
    {a b u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : u ∈ Icc (shift + clock a) (shift + clock b)) :
    ∃ t ∈ Icc a b, u = shift + clock t := by
  have hu0 : 0 ≤ u - shift := by
    have hh := hc.1.2.1 a ha
    linarith only [hu.1, hh]
  let t := originalClockTime β X shift (u - shift)
  have ht0 : 0 ≤ t := hc.2.2.1 _ hu0
  have heq : clock t = u - shift := hc.2.2.2.2 _ hu0
  have hat : a ≤ t := by
    by_contra hh
    have hlt := hc.2.1 ht0 ha (lt_of_not_ge hh)
    rw [heq] at hlt
    linarith only [hlt, hu.1]
  have htb : t ≤ b := by
    by_contra hh
    have hlt := hc.2.1 (ha.trans hab) ht0 (lt_of_not_ge hh)
    rw [heq] at hlt
    linarith only [hlt, hu.2]
  exact ⟨t, ⟨hat, htb⟩, by linarith only [heq]⟩

theorem exists_time_Ico {β shift : ℝ} {X : ℝ → Configuration n d}
    {clock : ℝ → ℝ} (hc : ClockRelation β X shift clock)
    {a b u : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hu : u ∈ Ico (shift + clock a) (shift + clock b)) :
    ∃ t ∈ Ico a b, u = shift + clock t := by
  obtain ⟨t, ht, heq⟩ := exists_time_Icc hc ha hab ⟨hu.1, hu.2.le⟩
  refine ⟨t, ⟨ht.1, lt_of_le_of_ne ht.2 ?_⟩, heq⟩
  intro htb
  rw [htb] at heq
  exact (ne_of_lt hu.2) heq

theorem shifted_clock_mem_Icc {β shift : ℝ} {X : ℝ → Configuration n d}
    {clock : ℝ → ℝ} (hc : ClockRelation β X shift clock)
    {a b t : ℝ} (ha : 0 ≤ a) (ht : t ∈ Icc a b) :
    shift + clock t ∈ Icc (shift + clock a) (shift + clock b) := by
  have hleft := hc.2.1.monotoneOn ha (ha.trans ht.1) ht.1
  have hright := hc.2.1.monotoneOn (ha.trans ht.1) ((ha.trans ht.1).trans ht.2) ht.2
  exact ⟨by linarith only [hleft], by linarith only [hright]⟩

end Metastability.PlateauClockTransfer
