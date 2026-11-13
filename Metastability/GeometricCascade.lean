import Metastability.CascadePreparation
import Metastability.CascadeStep
import Metastability.FiniteChain

/-! Finite geometric induction from visible source data, with actual stage times. -/
noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace Metastability.GeometricCascade
open Source CapEnlargement ActiveScales ActiveSourceLaw CascadeStep
variable {n N d : ℕ}

theorem admissible_parameters (n : ℕ) (hn : 0 < n) :
    ∃ κ CStar : ℝ, PlateauStability.kappaThreshold n < κ ∧ 0 < CStar ∧
      8 * κ / (1 / (4 * (n : ℝ))) < CStar := by
  let κ := PlateauStability.kappaThreshold n + 1
  have hκ : 0 < κ := by
    have := PlateauStability.kappaThreshold_gt_four n
    dsimp [κ]
    linarith
  exact ⟨κ, PostMergeContraction.tighteningConstant n κ, by dsimp [κ]; linarith,
    PostMergeContraction.tighteningConstant_pos n hn κ hκ,
    PostMergeContraction.tighteningConstant_margin n hn κ hκ⟩

theorem last_parent (T : CollisionTree n N) (l : Fin N) (hl : l.val + 1 = N) :
    T.parent l = Finset.univ := by
  have hm : T.parent l ∈ T.partition l.succ := by
    rw [T.merge l]
    exact Finset.mem_insert_self _ _
  have he : l.succ = Fin.last N := Fin.ext hl
  rw [he, T.final_partition, Finset.mem_singleton] at hm
  exact hm

theorem accumulated_error (T : CollisionTree n N) (model : Model) (l : Fin N)
    (a b L R : ℝ)
    (ha : |a - jumpTime model T l.castSucc| ≤ (l.val : ℝ) * L * R)
    (hb : |b - a - 1 / (2 * stageRate model T l)| ≤ L * R) :
    |b - jumpTime model T l.succ| ≤ (l.succ.val : ℝ) * L * R := by
  rw [TreeDynamics.jumpTime_succ T model l]
  have he : b - (jumpTime model T l.castSucc + 1 / (2 * stageRate model T l)) =
      (a - jumpTime model T l.castSucc) + (b - a - 1 / (2 * stageRate model T l)) := by ring
  rw [he]
  have hh := (abs_add_le (a - jumpTime model T l.castSucc)
    (b - a - 1 / (2 * stageRate model T l))).trans (add_le_add ha hb)
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
  nlinarith only [hh]

/-- The complete finite geometric cascade, with one threshold for the tree.
It applies to any literal clock after the common preparation shift. Clock
existence is also produced from the actual ODE. No center-propagation or
asymptotic trajectory estimate is an input. -/
theorem geometric_cascade (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ)
    (hκ : PlateauStability.kappaThreshold n < κ) (model : Model) (CStar : ℝ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∃ K : ℝ, 0 < K ∧ ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ X : ℝ → Configuration n d, Solves model β X → VisiblePrepared hN C β (X 0) →
      (∃ clock : ℝ → ℝ, ClockRelation β X (CStar * β) clock) ∧
      ∀ clock : ℝ → ℝ, ClockRelation β X (CStar * β) clock →
      ∀ (i j : Fin N → Fin n), (∀ l, i l ∈ T.left l) → (∀ l, j l ∈ T.right l) →
      ∃ s : Fin (N + 1) → ℝ, ∃ hit complete : Fin N → ℝ,
        s 0 = 0 ∧ (∀ r, 0 ≤ s r) ∧
        (∀ l, EntryGeometry T C β κ l (accelerated X (CStar * β) clock (s l.castSucc))) ∧
        (∀ r, |s r - jumpTime model T r| ≤ K * (Real.log (Real.log β) / Real.log β)) ∧
        (∀ l : Fin N,
          hit l ∈ Ioo (s l.castSucc) (s l.castSucc + (1 + 1 / (2 * stageRate model T l))) ∧
          complete l ∈ Ioc (hit l) (hit l + 20 * n * (Real.log (Real.log β) / Real.log β)) ∧
          complete l ≤ s l.succ ∧
          IsLeast {t : ℝ | s l.castSucc ≤ t ∧
            angularDist (accelerated X (CStar * β) clock t (i l))
              (accelerated X (CStar * β) clock t (j l)) = mesoscopicScale β} (hit l) ∧
          IsLeast {t : ℝ | s l.castSucc ≤ t ∧ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
            angularDist (accelerated X (CStar * β) clock t p)
              (accelerated X (CStar * β) clock t q) ≤ clockCutoff β} (complete l) ∧
          |hit l - jumpTime model T l.succ| ≤ K * (Real.log (Real.log β) / Real.log β) ∧
          |complete l - jumpTime model T l.succ| ≤ K * (Real.log (Real.log β) / Real.log β) ∧
          (∀ t ∈ Icc (s l.castSucc) (complete l),
            StageHyp T C β κ (entryMultiplier l + 1) l (accelerated X (CStar * β) clock t) ∧
            1 - ⟪(accelerated X (CStar * β) clock t (i l)).val,
              (accelerated X (CStar * β) clock t (j l)).val⟫ ≤ upperBarrier C l + treeMargin hN C) ∧
          (∀ t ∈ Icc (s l.castSucc) (hit l), mesoscopicScale β ≤
            angularDist (accelerated X (CStar * β) clock t (i l))
              (accelerated X (CStar * β) clock t (j l))) ∧
          (∀ t ∈ Icc (hit l) (complete l),
            angularDist (accelerated X (CStar * β) clock t (i l))
              (accelerated X (CStar * β) clock t (j l)) ≤ mesoscopicScale β) ∧
          (∀ t ∈ Icc (s l.castSucc) (complete l), ∀ m : Fin N, l < m →
            ∃ p ∈ T.parent m, ∃ q ∈ T.parent m,
              7 * treeMargin hN C ≤ angularDist (accelerated X (CStar * β) clock t p)
                (accelerated X (CStar * β) clock t q) ∧
              visibleScale β < angularDist (accelerated X (CStar * β) clock t p)
                (accelerated X (CStar * β) clock t q)) ∧
          (l.val + 1 = N → s l.succ = complete l) ∧
          (∀ k : Fin N, k.castSucc = l.succ →
            s l.succ = originalClockTime β X (CStar * β) (clock (complete l) + CStar * β) ∧
            clock (s l.succ) = clock (complete l) + CStar * β ∧
            s l.succ - complete l ≤ CStar * β / Real.log β *
              Real.exp (-β * (lowerBarrier C k - treeMargin hN C)) ∧
            (∀ t ∈ Icc (complete l) (s l.succ),
              (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
                angularDist (accelerated X (CStar * β) clock t p) (C (T.currentNode k D hD)).center <
                  (C (T.currentNode k D hD)).radius + entryMultiplier k * enlargementScale β) ∧
              (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
                angularDist (accelerated X (CStar * β) clock t p)
                  (accelerated X (CStar * β) clock t q) ≤ clockCutoff β)) ∧
            (∀ t ∈ Icc (complete l) (s l.succ), ∀ D ∈ T.partition k.castSucc,
              ∀ p ∈ D, ∀ q ∈ D,
                angularDist (accelerated X (CStar * β) clock t p)
                  (accelerated X (CStar * β) clock (complete l) q) ≤ 6 * clockCutoff β))) ∧
        (∀ p q : Fin n,
          angularDist (accelerated X (CStar * β) clock (s (Fin.last N)) p)
            (accelerated X (CStar * β) clock (s (Fin.last N)) q) ≤ clockCutoff β) := by
  classical
  have hκ0 : 0 < κ := (by norm_num : (0 : ℝ) < 4).trans
    ((PlateauStability.kappaThreshold_gt_four n).trans hκ)
  have hC0 : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ0)
    (BlockContraction.contraction_constant_pos n (TreeDynamics.particle_pos T))).trans hCStar
  obtain ⟨Ks, hKs, hstages⟩ := CascadeStep.all_stages T hN C hC κ hκ model CStar hCStar
  let L : ℝ := (∑ l : Fin N, |Ks l|) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hKL : ∀ l, Ks l ≤ L := by
    intro l
    have hh : |Ks l| ≤ ∑ r : Fin N, |Ks r| :=
      Finset.single_le_sum (fun r _ => abs_nonneg (Ks r)) (Finset.mem_univ l)
    exact (le_abs_self _).trans (hh.trans (by dsimp [L]; linarith))
  obtain ⟨B, hB⟩ := eventually_atTop.mp
    (hstages.and (CascadePreparation.initial_at_multiplier T hN C hC κ CStar hκ0 hCStar))
  refine ⟨((N : ℝ) + 1) * L, by positivity, max B 2,
    lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro β hβ X hX hvisible
  obtain ⟨⟨hβ1, hR, hstep⟩, hprepare⟩ := hB β ((le_max_left _ _).trans hβ)
  obtain ⟨hinitial, hclock⟩ := hprepare.2 model X hX hvisible
  refine ⟨hclock, ?_⟩
  intro clock hc i j hi hj
  let Y := accelerated X (CStar * β) clock
  let Rβ := Real.log (Real.log β) / Real.log β
  have hshift : 0 ≤ CStar * β := mul_nonneg hC0.le (zero_lt_one.trans hβ1).le
  have hentry₀ : EntryGeometry T C β κ ⟨0, hN⟩ (Y 0) := by
    have hy : Y 0 = X (CStar * β) := by dsimp [Y, accelerated]; rw [hc.1.1, add_zero]
    rw [hy]
    refine ⟨fun D hD => (hinitial D hD).2.1, ?_⟩
    intro D hD p hp
    simpa only [entryMultiplier, Fin.val_mk, Nat.cast_zero, mul_zero, zero_add, one_mul,
      enlargementScale, neg_div] using (hinitial D hD).1 (CStar * β) ⟨hshift, le_rfl⟩ p hp
  let P : Fin (N + 1) → ℝ → Prop := fun r a =>
    0 ≤ a ∧ |a - jumpTime model T r| ≤ (r.val : ℝ) * L * Rβ ∧
    ∀ hr : r.val < N, EntryGeometry T C β κ ⟨r.val, hr⟩ (Y a)
  let Q : Fin N → ℝ → (ℝ × ℝ) → ℝ → Prop := fun l a o b =>
    o.1 ∈ Ioo a (a + (1 + 1 / (2 * stageRate model T l))) ∧
    o.2 ∈ Ioc o.1 (o.1 + 20 * n * Rβ) ∧ o.2 ≤ b ∧
    IsLeast {t : ℝ | a ≤ t ∧ angularDist (Y t (i l)) (Y t (j l)) = mesoscopicScale β} o.1 ∧
    IsLeast {t : ℝ | a ≤ t ∧ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (Y t p) (Y t q) ≤ clockCutoff β} o.2 ∧
    |o.1 - a - 1 / (2 * stageRate model T l)| ≤ L * Rβ ∧
    |o.2 - a - 1 / (2 * stageRate model T l)| ≤ L * Rβ ∧
    (∀ t ∈ Icc a o.2, StageHyp T C β κ (entryMultiplier l + 1) l (Y t) ∧
      1 - ⟪(Y t (i l)).val, (Y t (j l)).val⟫ ≤ upperBarrier C l + treeMargin hN C) ∧
    (∀ t ∈ Icc a o.1, mesoscopicScale β ≤ angularDist (Y t (i l)) (Y t (j l))) ∧
    (∀ t ∈ Icc o.1 o.2, angularDist (Y t (i l)) (Y t (j l)) ≤ mesoscopicScale β) ∧
    (∀ t ∈ Icc a o.2, ∀ m : Fin N, l < m → ∃ p ∈ T.parent m, ∃ q ∈ T.parent m,
      7 * treeMargin hN C ≤ angularDist (Y t p) (Y t q) ∧ visibleScale β < angularDist (Y t p) (Y t q)) ∧
    (l.val + 1 = N → b = o.2) ∧
    (∀ k : Fin N, k.castSucc = l.succ →
      b = originalClockTime β X (CStar * β) (clock o.2 + CStar * β) ∧
      clock b = clock o.2 + CStar * β ∧
      b - o.2 ≤ CStar * β / Real.log β * Real.exp (-β * (lowerBarrier C k - treeMargin hN C)) ∧
      EntryGeometry T C β κ k (Y b) ∧
      (∀ t ∈ Icc o.2 b,
        (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
          angularDist (Y t p) (C (T.currentNode k D hD)).center <
            (C (T.currentNode k D hD)).radius + entryMultiplier k * enlargementScale β) ∧
        (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
          angularDist (Y t p) (Y t q) ≤ clockCutoff β)) ∧
      (∀ t ∈ Icc o.2 b, ∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (Y t p) (Y o.2 q) ≤ 6 * clockCutoff β))
  have hp₀ : P 0 0 := by
    refine ⟨le_rfl, ?_, fun _ => hentry₀⟩
    simp only [TreeDynamics.jumpTime_zero T model, sub_self, abs_zero, Fin.val_zero,
      Nat.cast_zero, zero_mul, le_refl]
  have htransition : ∀ l : Fin N, ∀ a, P l.castSucc a →
      ∃ o b, P l.succ b ∧ Q l a o b := by
    intro l a ha
    obtain ⟨tm, htm, tp, htp, b, hb, hm, hp, hem, hep, heb, hgeo, hmeso, hterm, hfut, hlast, hnxt⟩ :=
      hstep l X hX (CStar * β) hshift clock hc a ha.1 (i l) (j l) (hi l) (hj l) (ha.2.2 l.isLt)
    have hbound : Ks l * Rβ ≤ L * Rβ := mul_le_mul_of_nonneg_right (hKL l) hR
    have hem' := hem.trans hbound
    have hep' := hep.trans hbound
    have heb' := heb.trans hbound
    refine ⟨(tm, tp), b, ⟨ha.1.trans (htm.1.le.trans (htp.1.le.trans hb)),
      accumulated_error T model l a b L Rβ ha.2.1 heb', ?_⟩,
      htm, htp, hb, hm, hp, hem', hep', hgeo, hmeso, hterm, hfut, hlast, hnxt⟩
    intro hr
    exact (hnxt ⟨l.val + 1, hr⟩ rfl).2.2.2.1
  obtain ⟨s, o, hs₀, hs, ho⟩ := FiniteChain.exists_chain P Q 0 hp₀ htransition
  have hglobal : ∀ r : Fin (N + 1), (r.val : ℝ) * L * Rβ ≤ ((N : ℝ) + 1) * L * Rβ := by
    intro r
    have hr : (r.val : ℝ) < (N : ℝ) + 1 := by exact_mod_cast r.isLt
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr.le hL.le) hR
  refine ⟨s, fun l => (o l).1, fun l => (o l).2, hs₀, fun r => (hs r).1,
    fun l => (hs l.castSucc).2.2 l.isLt,
    fun r => (hs r).2.1.trans (hglobal r), ?_, ?_⟩
  · intro l
    obtain ⟨htm, htp, hb, hm, hp, hem, hep, hgeo, hmeso, hterm, hfut, hlast, hnxt⟩ := ho l
    refine ⟨htm, htp, hb, hm, hp,
      (accumulated_error T model l _ _ L Rβ (hs l.castSucc).2.1 hem).trans (hglobal l.succ),
      (accumulated_error T model l _ _ L Rβ (hs l.castSucc).2.1 hep).trans (hglobal l.succ),
      hgeo, hmeso, hterm, hfut, hlast, ?_⟩
    intro k hk
    obtain ⟨hdef, hclock', hlength, _, hcaps, hmotion⟩ := hnxt k hk
    exact ⟨hdef, hclock', hlength, hcaps, hmotion⟩
  · let last : Fin N := ⟨N - 1, by omega⟩
    have hl : last.val + 1 = N := by dsimp [last]; omega
    have hls : last.succ = Fin.last N := Fin.ext hl
    obtain ⟨_, _, _, _, hp, _, _, _, _, _, _, hlast, _⟩ := ho last
    have he := hlast hl
    rw [hls] at he
    have hroot := last_parent T last hl
    intro p q
    change angularDist (Y (s (Fin.last N)) p) (Y (s (Fin.last N)) q) ≤ _
    rw [he]
    exact hp.1.2 p (hroot.symm ▸ Finset.mem_univ p) q (hroot.symm ▸ Finset.mem_univ q)

end Metastability.GeometricCascade
