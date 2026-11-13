import Metastability.StageRestart
import Metastability.LiteralCenters

/-! A finite-uniform geometric step retaining all facts needed by the cascade. -/
noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace Metastability.CascadeStep
open Source CapEnlargement ActiveScales ActiveSourceLaw
variable {n N d : ℕ}

/-- The literal source enlargement multiplier at an entry stage. -/
def entryMultiplier (l : Fin N) : ℝ := 2 * (l.val : ℝ) + 1

/-- Stage entry geometry contains only the two pointwise inequalities in the
source induction: exponential diameters and prescribed cap membership. -/
def EntryGeometry (T : CollisionTree n N) (C : TreeCaps T d)
    (β κ : ℝ) (l : Fin N) (x : Configuration n d) : Prop :=
  (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
    angularDist (x p) (x q) ≤ Real.exp (-2 * κ * β)) ∧
  (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), ∀ p ∈ D,
    angularDist (x p) (C (T.currentNode l D hD)).center ≤
      (C (T.currentNode l D hD)).radius + entryMultiplier l * enlargementScale β)

theorem entryMultiplier_bounds (l : Fin N) :
    entryMultiplier l ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 3) := by
  have hl : (l.val : ℝ) < N := by exact_mod_cast l.isLt
  unfold entryMultiplier
  constructor
  · positivity
  · linarith only [hl]

theorem entryMultiplier_succ (l k : Fin N) (hk : k.castSucc = l.succ) :
    entryMultiplier k = entryMultiplier l + 2 := by
  have hh : k.val = l.val + 1 := congrArg Fin.val hk
  simp only [entryMultiplier, hh, Nat.cast_add, Nat.cast_one]
  ring

/-- One common eventual set covers all stages. The final merge uses its
completion as the terminal entry; every other merge produces the actual
post-tightening time and next entry geometry. -/
theorem all_stages (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ)
    (hκ : PlateauStability.kappaThreshold n < κ) (model : Model) (CStar : ℝ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∃ K : Fin N → ℝ, (∀ l, 0 < K l) ∧
      ∀ᶠ β : ℝ in atTop, 1 < β ∧ 0 ≤ Real.log (Real.log β) / Real.log β ∧
      ∀ (l : Fin N) (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ s : ℝ, 0 ≤ s → ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      EntryGeometry T C β κ l (accelerated X shift clock s) →
      ∃ t₁ ∈ Ioo s (s + (1 + 1 / (2 * stageRate model T l))),
      ∃ t₂ ∈ Ioc t₁ (t₁ + 20 * n * (Real.log (Real.log β) / Real.log β)),
      ∃ snext : ℝ, t₂ ≤ snext ∧
        IsLeast {t : ℝ | s ≤ t ∧
          angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) = mesoscopicScale β} t₁ ∧
        IsLeast {t : ℝ | s ≤ t ∧ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β} t₂ ∧
        |t₁ - s - 1 / (2 * stageRate model T l)| ≤ K l * (Real.log (Real.log β) / Real.log β) ∧
        |t₂ - s - 1 / (2 * stageRate model T l)| ≤ K l * (Real.log (Real.log β) / Real.log β) ∧
        |snext - s - 1 / (2 * stageRate model T l)| ≤ K l * (Real.log (Real.log β) / Real.log β) ∧
        (∀ t ∈ Icc s t₂,
          StageHyp T C β κ (entryMultiplier l + 1) l (accelerated X shift clock t) ∧
          1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
            upperBarrier C l + treeMargin hN C) ∧
        (∀ t ∈ Icc s t₁, mesoscopicScale β ≤
          angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) ∧
        (∀ t ∈ Icc t₁ t₂, angularDist (accelerated X shift clock t i)
          (accelerated X shift clock t j) ≤ mesoscopicScale β) ∧
        (∀ t ∈ Icc s t₂, ∀ m : Fin N, l < m →
          ∃ p ∈ T.parent m, ∃ q ∈ T.parent m,
            7 * treeMargin hN C ≤ angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ∧
            visibleScale β < angularDist (accelerated X shift clock t p) (accelerated X shift clock t q)) ∧
        (l.val + 1 = N → snext = t₂) ∧
        (∀ (k : Fin N), k.castSucc = l.succ →
          snext = originalClockTime β X shift (clock t₂ + CStar * β) ∧
          clock snext = clock t₂ + CStar * β ∧
          snext - t₂ ≤ CStar * β / Real.log β *
            Real.exp (-β * (lowerBarrier C k - treeMargin hN C)) ∧
          EntryGeometry T C β κ k (accelerated X shift clock snext) ∧
          (∀ t ∈ Icc t₂ snext,
            (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
              angularDist (accelerated X shift clock t p) (C (T.currentNode k D hD)).center <
                (C (T.currentNode k D hD)).radius + entryMultiplier k * enlargementScale β) ∧
            (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
              angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β)) ∧
          (∀ t ∈ Icc t₂ snext, ∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
            angularDist (accelerated X shift clock t p) (accelerated X shift clock t₂ q) ≤
              6 * clockCutoff β)) := by
  classical
  have hκ0 : 0 < κ := (by norm_num : (0 : ℝ) < 4).trans
    ((PlateauStability.kappaThreshold_gt_four n).trans hκ)
  choose K hK B hB hcompletion using fun l : Fin N =>
    CompletionCollision.stage_completion T hN C hC κ hκ model l
  choose P hP hpost using fun k : Fin N =>
    PostMergeStep.tightening_from_caps T hN C hC k κ CStar hκ0 hCStar
  choose J hJ Q hQ hplateau using fun l : Fin N =>
    PlateauCollision.plateau_stability T hN C hC κ hκ model l
  have hBs : ∀ᶠ β : ℝ in atTop, ∀ l, B l ≤ β :=
    eventually_all.mpr (fun l => eventually_ge_atTop (B l))
  have hPs : ∀ᶠ β : ℝ in atTop, ∀ l, P l ≤ β :=
    eventually_all.mpr (fun l => eventually_ge_atTop (P l))
  have hQs : ∀ᶠ β : ℝ in atTop, ∀ l, Q l ≤ β :=
    eventually_all.mpr (fun l => eventually_ge_atTop (Q l))
  refine ⟨fun l => K l + 20 * n + 1, fun l => by have := hK l; positivity, ?_⟩
  filter_upwards [hBs, hPs, hQs, eventually_clock_parameters κ 1 hκ0 (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    ContractionScale.tendsto_visibleScale.eventually (gt_mem_nhds (half_pos Real.pi_pos))]
    with β hBs hPs hQs hsc hlog hvisπ
  have hβ : 1 < β := (hB ⟨0, hN⟩).trans_le (hBs _)
  have hR : 0 ≤ Real.log (Real.log β) / Real.log β :=
    div_nonneg (Real.log_nonneg hlog) (Real.log_pos hβ).le
  have hcutπ : clockCutoff β < Real.pi / 2 := by
    have hv0 := ContractionScale.visibleScale_pos hβ
    unfold clockCutoff
    linarith only [hvisπ, hv0]
  refine ⟨hβ, hR, ?_⟩
  intro l X hX shift hshift clock hc s hs i j hi hj he
  have hM := entryMultiplier_bounds l
  have hM0 : entryMultiplier l ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4) :=
    ⟨hM.1, by linarith only [hM.2]⟩
  obtain ⟨t₁, ht₁, t₂, ht₂, hhit, hleast₁, herr, hleast₂, _, hgeometry, hterminal, hfuture⟩ :=
    hcompletion l β (hBs l) (entryMultiplier l) hM0 X hX shift hshift clock hc s hs i j hi hj he.1 he.2
  obtain ⟨t₁', _, _, hbefore, hleast₁', _, _, _⟩ :=
    hplateau l β (hQs l) (entryMultiplier l) hM0 X hX shift hshift clock hc s hs i j hi hj he.1 he.2
  have heq : t₁' = t₁ := hleast₁'.unique hleast₁
  subst t₁'
  have hmeso : ∀ t ∈ Icc s t₁, mesoscopicScale β ≤
      angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact (hbefore t ⟨ht.1, hlt⟩).le
    · exact hhit.ge
  have herr₁ : |t₁ - s - 1 / (2 * stageRate model T l)| ≤
      (K l + 20 * n + 1) * (Real.log (Real.log β) / Real.log β) := by
    have hle : K l ≤ K l + 20 * n + 1 := by
      have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith only [hnR]
    exact herr.trans (mul_le_mul_of_nonneg_right hle hR)
  have herr₂ : |t₂ - s - 1 / (2 * stageRate model T l)| ≤
      (K l + 20 * n) * (Real.log (Real.log β) / Real.log β) := by
    have heq : t₂ - s - 1 / (2 * stageRate model T l) =
        (t₁ - s - 1 / (2 * stageRate model T l)) + (t₂ - t₁) := by ring
    rw [heq]
    have htri := abs_add_le (t₁ - s - 1 / (2 * stageRate model T l)) (t₂ - t₁)
    rw [abs_of_nonneg (sub_nonneg.mpr ht₂.1.le)] at htri
    nlinarith only [htri, herr, ht₂.2]
  have herr₂' := herr₂.trans (mul_le_mul_of_nonneg_right
    (show K l + 20 * n ≤ K l + 20 * n + 1 by linarith) hR)
  by_cases hn : l.val + 1 < N
  · let k : Fin N := ⟨l.val + 1, hn⟩
    have hk : k.castSucc = l.succ := rfl
    have hst₂ : s ≤ t₂ := ht₁.1.le.trans ht₂.1.le
    obtain ⟨hd₂, hc₂⟩ := NextStageGeometry.completed_partition T C l k hk β κ
      (entryMultiplier l + 1) (accelerated X shift clock t₂)
      (hgeometry t₂ ⟨hst₂, le_rfl⟩).1 hsc.2.2.1 hleast₂.1.2
    have hM1 : entryMultiplier l + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4) :=
      ⟨by linarith only [hM.1], by linarith only [hM.2]⟩
    obtain ⟨sn, hsn, hdef, hclock, hdur, hratio, hcaps, htight, hcenters⟩ :=
      hpost k β (hPs k) (entryMultiplier l + 1) hM1 model X hX shift hshift clock hc
        t₂ (hs.trans hst₂) hd₂ hc₂
    have herrn : |sn - s - 1 / (2 * stageRate model T l)| ≤
        (K l + 20 * n + 1) * (Real.log (Real.log β) / Real.log β) := by
      have heq : sn - s - 1 / (2 * stageRate model T l) =
          (t₂ - s - 1 / (2 * stageRate model T l)) + (sn - t₂) := by ring
      rw [heq]
      have htri := abs_add_le (t₂ - s - 1 / (2 * stageRate model T l)) (sn - t₂)
      rw [abs_of_nonneg (sub_nonneg.mpr hsn)] at htri
      nlinarith only [htri, herr₂, hratio]
    refine ⟨t₁, ht₁, t₂, ht₂, sn, hsn, hleast₁, hleast₂, herr₁, herr₂', herrn,
      hgeometry, hmeso, hterminal, hfuture, (by omega), ?_⟩
    intro k' hk'
    have hkk : k' = k := Fin.ext
      (congrArg (fun p : Fin (N + 1) => p.val) (hk'.trans hk.symm))
    subst k'
    have hMnext : entryMultiplier l + 1 + 1 = entryMultiplier k := by
      rw [entryMultiplier_succ l k hk]
      ring
    have hcaps' : ∀ t ∈ Icc t₂ sn,
        (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
          angularDist (accelerated X shift clock t p) (C (T.currentNode k D hD)).center <
            (C (T.currentNode k D hD)).radius + entryMultiplier k * enlargementScale β) ∧
        (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) := by
      simpa only [hMnext] using hcaps
    refine ⟨hdef, hclock, hdur, ⟨htight, fun D hD p hp =>
      ((hcaps' sn ⟨hsn, le_rfl⟩).1 D hD p hp).le⟩, hcaps', ?_⟩
    intro t ht D hD p hp q hq
    obtain ⟨_, z₀, hz₀, hzall⟩ := hcenters D hD
    obtain ⟨_, z, hz, hmove⟩ := hzall t ht
    have hh := LiteralCenters.particle_displacement D (T.block_nonempty _ _ hD)
      (accelerated X shift clock t) (accelerated X shift clock t₂) z z₀ hz hz₀
      (clockCutoff β) (4 * clockCutoff β) hcutπ ((hcaps' t ht).2 D hD)
      (hd₂ D hD) hmove p q hp hq
    linarith only [hh]
  · refine ⟨t₁, ht₁, t₂, ht₂, t₂, le_rfl, hleast₁, hleast₂, herr₁, herr₂', herr₂',
      hgeometry, hmeso, hterminal, hfuture, fun _ => rfl, ?_⟩
    intro k hk
    have hh : k.val = l.val + 1 := congrArg Fin.val hk
    have := k.isLt
    omega

end Metastability.CascadeStep
