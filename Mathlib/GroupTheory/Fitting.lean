/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Algebra.Group.Subgroup.Pointwise

section

private theorem Subgroup.commutator_sup_left' {G : Type*} [Group G] (H K N : Subgroup G) [N.Normal]
    [(⁅H, N⁆ ⊔ ⁅K, N⁆).Normal] : ⁅H ⊔ K, N⁆ = ⁅H, N⁆ ⊔ ⁅K, N⁆ := by
  refine le_antisymm ?_
    (sup_le (commutator_mono_left le_sup_left) (commutator_mono_left le_sup_right))
  have hH : ⁅H, N⁆ ≤ ⁅H, N⁆ ⊔ ⁅K, N⁆ := le_sup_left
  have hK : ⁅K, N⁆ ≤ ⁅H, N⁆ ⊔ ⁅K, N⁆ := le_sup_right
  rw [← QuotientGroup.ker_mk' (⁅H, N⁆ ⊔ ⁅K, N⁆), ← Subgroup.map_eq_bot_iff,
    map_commutator, Subgroup.commutator_eq_bot_iff_le_centralizer] at hH hK ⊢
  rw [map_sup]
  exact sup_le hH hK

theorem Subgroup.commutator_sup_left {G : Type*} [Group G] (H K N : Subgroup G) [N.Normal] :
    ⁅H ⊔ K, N⁆ = ⁅H, N⁆ ⊔ ⁅K, N⁆ := by
  let M := H ⊔ K ⊔ N
  have hHM : H ≤ M := le_sup_of_le_left le_sup_left
  have hKM : K ≤ M := le_sup_of_le_left le_sup_right
  have hNM : N ≤ M := le_sup_right
  have hHNM : ⁅H, N⁆ ≤ M := commutator_le_of_le hHM hNM
  have hKNM : ⁅K, N⁆ ≤ M := commutator_le_of_le hKM hNM
  suffices (⁅H.subgroupOf M, N.subgroupOf M⁆ ⊔ ⁅K.subgroupOf M, N.subgroupOf M⁆).Normal by
    simpa [← map_subtype_inj, map_sup, map_commutator, hHM, hKM, hNM] using
      commutator_sup_left' (H.subgroupOf M) (K.subgroupOf M) (N.subgroupOf M)
  suffices M ≤ normalizer (⁅H, N⁆ ⊔ ⁅K, N⁆ : Subgroup G) by
    convert Subgroup.normal_subgroupOf_of_le_normalizer this
    simp [← map_subtype_inj, map_sup, map_commutator, hHM, hKM, hNM, hHNM, hKNM]
  have hHKN : ⁅H, N⁆ ⊔ ⁅K, N⁆ ≤ N := sup_le (commutator_le_right H N) (commutator_le_right K N)
  refine sup_le (sup_le ?_ ?_) ?_
  · grw [le_normalizer_iff_commutator_le_right, hHKN, ← le_sup_left]
  · grw [le_normalizer_iff_commutator_le_right, hHKN, ← le_sup_right]
  · grw [← normalizer_inf_normalizer_le_normalizer_sup, ← normalizer_commutator_ge_right,
      ← normalizer_commutator_ge_right, inf_idem]

theorem Subgroup.commutator_sup_right {G : Type*} [Group G] (N H K : Subgroup G) [N.Normal] :
    ⁅N, H ⊔ K⁆ = ⁅N, H⁆ ⊔ ⁅N, K⁆ := by
  simp_rw [commutator_comm N, commutator_sup_left]

local notation "lcs" => Subgroup.lowerCentralSeries

theorem Subgroup.lowerCentralSeries_sup_add_le
    {G : Type*} [Group G] {H K : Subgroup G} [H.Normal] [K.Normal] {m n : ℕ} :
    lcs (H ⊔ K) (m + n) ≤ lcs H m ⊔ lcs K n := by
  suffices P : ∀ k {m n}, m + n = k → lcs (H ⊔ K) k ≤ lcs H m ⊔ lcs K n from P (m + n) rfl
  intro k
  induction k with
  | zero => simp
  | succ k hk =>
    intro m n hmn
    rw [lowerCentralSeries_succ, commutator_sup_right]
    apply sup_le
    · cases m
      case zero => grw [lowerCentralSeries_zero, commutator_le_right, ← le_sup_left]
      case succ m =>
        rw [add_right_comm, add_left_inj] at hmn
        grw [hk hmn, commutator_sup_left, commutator_le_left (lcs K n), lowerCentralSeries_succ]
    · cases n
      case zero => grw [lowerCentralSeries_zero, commutator_le_right, ← le_sup_right]
      case succ n =>
        rw [← add_assoc, add_left_inj] at hmn
        grw [hk hmn, commutator_sup_left, commutator_le_left, lowerCentralSeries_succ]

end
