import Metastability.CompactStages

/-! Analytic gluing of finitely many moving energy plateaus. This conditional
transfer lemma is consumed after the actual cascade produces its windows and
energy estimates; it does not assert those dynamical hypotheses. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Metastability.CascadeEnergyTransfer
open Source CompactStages
variable {n N : ℕ}

theorem uniform_staircase_of_windows (T : CollisionTree n N) (hN : 0 < N) (model : Model)
    (f : ℝ → ℝ → ℝ) (s hit : ℝ → Fin N → ℝ) (last : ℝ → ℝ)
    (e q : ℝ → ℝ) (he : Tendsto e atTop (𝓝 0)) (hq : Tendsto q atTop (𝓝 0))
    (hs : ∀ l : Fin N, Tendsto (fun β => s β l) atTop (𝓝 (jumpTime model T l.castSucc)))
    (hhit : ∀ l : Fin N, Tendsto (fun β => hit β l) atTop (𝓝 (jumpTime model T l.succ)))
    (hlast : Tendsto last atTop (𝓝 (jumpTime model T (Fin.last N))))
    (hzero : ∀ᶠ β : ℝ in atTop, s β ⟨0, hN⟩ = 0)
    (hstage : ∀ᶠ β : ℝ in atTop, ∀ l : Fin N, ∀ t ∈ Icc (s β l) (hit β l),
      |f β t - plateauEnergy T l.castSucc| ≤ e β)
    (hterminal : ∀ᶠ β : ℝ in atTop, ∀ t ≥ last β, |f β t - 1| ≤ q β)
    (K : Set ℝ) (hK : IsCompact K) (hK0 : K ⊆ Ici 0)
    (havoid : ∀ t ∈ K, ∀ l : Fin N, t ≠ jumpTime model T l.succ) :
    ∀ ε > 0, ∀ᶠ β : ℝ in atTop, ∀ t ∈ K, |f β t - staircase model T t| < ε := by
  have hwindow : ∀ l : Fin N, ∀ᶠ β : ℝ in atTop,
      ∀ t ∈ K ∩ Icc (jumpTime model T l.castSucc) (jumpTime model T l.succ),
        t ∈ Icc (s β l) (hit β l) := by
    intro l
    let Kl := K ∩ Icc (jumpTime model T l.castSucc) (jumpTime model T l.succ)
    have hcompact : IsCompact Kl := hK.inter_right isClosed_Icc
    have hupper : Kl ⊆ Iio (jumpTime model T l.succ) := by
      intro t ht
      exact lt_of_le_of_ne ht.2.2 (havoid t ht.1 l)
    have habove := eventually_above_compact hcompact hupper (hhit l)
    by_cases h0 : l.val = 0
    · have hl0 : l = ⟨0, hN⟩ := Fin.ext h0
      filter_upwards [hzero, habove] with β hz hb
      intro t ht
      exact ⟨by rw [hl0, hz]; exact hK0 ht.1, (hb t ht).le⟩
    · have hlpos : 0 < l.val := Nat.pos_of_ne_zero h0
      let r : Fin N := ⟨l.val - 1, by omega⟩
      have hr : r.succ = l.castSucc := Fin.ext (by dsimp [r]; omega)
      have hlower : Kl ⊆ Ioi (jumpTime model T l.castSucc) := by
        intro t ht
        apply lt_of_le_of_ne ht.2.1
        intro heq
        exact havoid t ht.1 r (heq.symm.trans (congrArg (jumpTime model T) hr.symm))
      have hbelow := eventually_below_compact hcompact hlower (hs l)
      filter_upwards [hbelow, habove] with β hb hu
      intro t ht
      exact ⟨(hb t ht).le, (hu t ht).le⟩
  have hlastwindow : ∀ᶠ β : ℝ in atTop,
      ∀ t ∈ K ∩ Ici (jumpTime model T (Fin.last N)), last β ≤ t := by
    let r : Fin N := ⟨N - 1, by omega⟩
    have hr : r.succ = Fin.last N := Fin.ext (by dsimp [r]; omega)
    have hsub : K ∩ Ici (jumpTime model T (Fin.last N)) ⊆ Ioi (jumpTime model T (Fin.last N)) := by
      intro t ht
      change jumpTime model T (Fin.last N) < t
      apply lt_of_le_of_ne (show jumpTime model T (Fin.last N) ≤ t from ht.2)
      intro heq
      exact havoid t ht.1 r (heq.symm.trans (congrArg (jumpTime model T) hr.symm))
    exact (eventually_below_compact (hK.inter_right isClosed_Ici) hsub hlast).mono
      (fun _ h t ht => (h t ht).le)
  intro ε hε
  filter_upwards [eventually_all.mpr hwindow, hlastwindow, hstage, hterminal,
    he.eventually (gt_mem_nhds hε), hq.eventually (gt_mem_nhds hε)]
      with β hw hlw hst hterm hes hqs
  intro t ht
  rcases stage_or_terminal T model t (hK0 ht) with ⟨l, hl⟩ | hl
  · rw [staircase_on_stage T model l t hl]
    exact (hst l t (hw l t ⟨ht, hl.1, hl.2.le⟩)).trans_lt hes
  · rw [staircase_after_final T model t hl]
    exact (hterm t (hlw t ⟨ht, hl⟩)).trans_lt hqs

end Metastability.CascadeEnergyTransfer
