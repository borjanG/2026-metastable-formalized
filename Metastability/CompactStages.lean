import Metastability.TreeDynamics
import Mathlib.Topology.Order.Compact

/-! Finite plateau decomposition and uniform inclusion of compact time sets
in converging stage windows. These elementary helpers retain t=0 in the first
energy plateau and exclude each actual limiting jump. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Metastability.CompactStages
open Source
variable {n N : ℕ}

theorem staircase_on_stage (T : CollisionTree n N) (model : Model) (l : Fin N)
    (t : ℝ) (ht : t ∈ Ico (jumpTime model T l.castSucc) (jumpTime model T l.succ)) :
    staircase model T t = plateauEnergy T l.castSucc := by
  classical
  have hmono := TreeDynamics.jumpTime_strictMono T model
  have hlast : t < jumpTime model T (Fin.last N) :=
    ht.2.trans_le (hmono.monotone (Fin.le_last _))
  have hterm : ∀ k : Fin N,
      (jumpTime model T k.castSucc ≤ t ∧ t < jumpTime model T k.succ) ↔ k = l := by
    intro k
    constructor
    · intro hk
      apply Fin.ext
      have hkl : k.val ≤ l.val := by
        by_contra h
        have hv : l.succ ≤ k.castSucc := Fin.le_iff_val_le_val.mpr (by simpa using (by omega : l.val + 1 ≤ k.val))
        exact (not_lt_of_ge (hmono.monotone hv |>.trans hk.1)) ht.2
      have hlk : l.val ≤ k.val := by
        by_contra h
        have hv : k.succ ≤ l.castSucc := Fin.le_iff_val_le_val.mpr (by simpa using (by omega : k.val + 1 ≤ l.val))
        exact (not_lt_of_ge (hmono.monotone hv |>.trans ht.1)) hk.2
      omega
    · rintro rfl
      exact ht
  simp only [staircase, hterm, not_le.mpr hlast, if_false, add_zero]
  simp

theorem staircase_after_final (T : CollisionTree n N) (model : Model)
    (t : ℝ) (ht : jumpTime model T (Fin.last N) ≤ t) : staircase model T t = 1 := by
  have hterm : ∀ l : Fin N, ¬ (jumpTime model T l.castSucc ≤ t ∧ t < jumpTime model T l.succ) := by
    intro l hl
    have hh := (TreeDynamics.jumpTime_strictMono T model).monotone (Fin.le_last l.succ)
    exact (not_lt_of_ge (hh.trans ht)) hl.2
  simp only [staircase, hterm, if_false, Finset.sum_const_zero, ht, if_true, zero_add]

/-- Every nonnegative time belongs to a stage or the terminal interval. -/
theorem stage_or_terminal (T : CollisionTree n N) (model : Model) (t : ℝ) (ht : 0 ≤ t) :
    (∃ l : Fin N, t ∈ Ico (jumpTime model T l.castSucc) (jumpTime model T l.succ)) ∨
      jumpTime model T (Fin.last N) ≤ t := by
  by_cases hend : jumpTime model T (Fin.last N) ≤ t
  · exact Or.inr hend
  have hex : ∃ k : ℕ, ∃ hk : k < N + 1, t < jumpTime model T ⟨k, hk⟩ :=
    ⟨N, Nat.lt_succ_self N, lt_of_not_ge hend⟩
  obtain ⟨hkN, hkt⟩ := Nat.find_spec hex
  have hk0 : 0 < Nat.find hex := by
    by_contra h
    have heq : Nat.find hex = 0 := by omega
    have hf : (⟨Nat.find hex, hkN⟩ : Fin (N + 1)) = 0 := Fin.ext heq
    rw [hf, TreeDynamics.jumpTime_zero] at hkt
    exact (not_lt_of_ge ht) hkt
  let l : Fin N := ⟨Nat.find hex - 1, by omega⟩
  have heq : l.succ = (⟨Nat.find hex, hkN⟩ : Fin (N + 1)) := Fin.ext (by dsimp [l]; omega)
  refine Or.inl ⟨l, ?_, by simpa only [heq] using hkt⟩
  by_contra h
  have hh : ∃ hl : l.val < N + 1, t < jumpTime model T ⟨l.val, hl⟩ :=
    ⟨l.castSucc.isLt, lt_of_not_ge h⟩
  have hmin := Nat.find_min' hex hh
  dsimp [l] at hmin
  omega

/-- A compact set strictly above a limiting entry is uniformly above nearby entries. -/
theorem eventually_below_compact {a : ℝ} {s : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hKa : K ⊆ Ioi a) (hs : Tendsto s atTop (𝓝 a)) :
    ∀ᶠ β : ℝ in atTop, ∀ t ∈ K, s β < t := by
  by_cases hne : K.Nonempty
  · obtain ⟨m, hm⟩ := hK.exists_isLeast hne
    filter_upwards [hs.eventually (gt_mem_nhds (hKa hm.1))] with β hb
    intro t ht
    exact hb.trans_le (hm.2 ht)
  · exact Filter.Eventually.of_forall (fun _ t ht => (hne ⟨t, ht⟩).elim)

/-- A compact set strictly below a limiting hit is uniformly below nearby hits. -/
theorem eventually_above_compact {b : ℝ} {s : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hKb : K ⊆ Iio b) (hs : Tendsto s atTop (𝓝 b)) :
    ∀ᶠ β : ℝ in atTop, ∀ t ∈ K, t < s β := by
  by_cases hne : K.Nonempty
  · obtain ⟨m, hm⟩ := hK.exists_isGreatest hne
    filter_upwards [hs.eventually (lt_mem_nhds (hKb hm.1))] with β hb
    intro t ht
    exact (hm.2 ht).trans_lt hb
  · exact Filter.Eventually.of_forall (fun _ t ht => (hne ⟨t, ht⟩).elim)

/-- A positive uniform amount of active time has elapsed on an interior compact set. -/
theorem exists_eventually_gap {a : ℝ} {s : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hKa : K ⊆ Ioi a) (hs : Tendsto s atTop (𝓝 a)) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ β : ℝ in atTop, ∀ t ∈ K, s β + η ≤ t := by
  by_cases hne : K.Nonempty
  · obtain ⟨m, hm⟩ := hK.exists_isLeast hne
    have ham : a < m := hKa hm.1
    refine ⟨(m - a) / 2, half_pos (sub_pos.mpr ham), ?_⟩
    have hnear : a < (m + a) / 2 := by linarith only [ham]
    filter_upwards [hs.eventually (gt_mem_nhds hnear)] with β hb
    intro t ht
    have hm' := hm.2 ht
    linarith only [hb, hm']
  · exact ⟨1, by norm_num, Filter.Eventually.of_forall (fun _ t ht => (hne ⟨t, ht⟩).elim)⟩

end Metastability.CompactStages
