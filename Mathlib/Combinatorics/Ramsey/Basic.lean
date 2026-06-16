/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Nat.Choose.Central

/-!
# Ramsey numbers

Define edge labellings, monochromatic subsets and ramsey numbers, and prove basic properties of
these.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

theorem neighborSet_sup {G H : SimpleGraph V} {x : V} :
    (G ⊔ H).neighborSet x = G.neighborSet x ∪ H.neighborSet x := by
  ext
  simp

theorem neighborSet_inf {G H : SimpleGraph V} {x : V} :
    (G ⊓ H).neighborSet x = G.neighborSet x ∩ H.neighborSet x := by
  ext
  simp

theorem neighborSet_iSup {ι : Type*} {s : ι → SimpleGraph V} {x : V} :
    (⨆ i, s i).neighborSet x = ⋃ i, (s i).neighborSet x := by
  ext
  simp

theorem neighborSet_iInf {ι : Type*} [Nonempty ι] {s : ι → SimpleGraph V} {x : V} :
    (⨅ i, s i).neighborSet x = ⋂ i, (s i).neighborSet x := by
  inhabit ι
  ext y
  simp only [mem_neighborSet, iInf_adj, Set.mem_iInter, and_iff_left_iff_imp]
  intro h
  exact (h default).ne

theorem neighborSet_disjoint {G H : SimpleGraph V} {x : V} (h : Disjoint G H) :
    Disjoint (G.neighborSet x) (H.neighborSet x) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← neighborSet_inf, h.eq_bot, neighborSet_bot]

theorem neighborFinset_bot {x : V} [Fintype (neighborSet ⊥ x)] :
    (⊥ : SimpleGraph V).neighborFinset x = ∅ := by
  ext
  simp

theorem neighborFinset_top [Fintype V] [DecidableEq V] {x : V} :
    (⊤ : SimpleGraph V).neighborFinset x = {x}ᶜ := by
  simp [← Finset.coe_inj, neighborSet_top]

theorem neighborFinset_sup [DecidableEq V] {G H : SimpleGraph V} {x : V}
    [Fintype ((G ⊔ H).neighborSet x)] [Fintype (G.neighborSet x)] [Fintype (H.neighborSet x)] :
    (G ⊔ H).neighborFinset x = G.neighborFinset x ∪ H.neighborFinset x := by
  simp [← Finset.coe_inj, neighborSet_sup]

theorem neighborFinset_inf [DecidableEq V] {G H : SimpleGraph V} {x : V}
    [Fintype ((G ⊓ H).neighborSet x)] [Fintype (G.neighborSet x)] [Fintype (H.neighborSet x)] :
    (G ⊓ H).neighborFinset x = G.neighborFinset x ∩ H.neighborFinset x := by
  simp [← Finset.coe_inj, neighborSet_inf]

theorem neighborFinset_disjoint {G H : SimpleGraph V} {x : V} [Fintype (G.neighborSet x)]
    [Fintype (H.neighborSet x)] (h : Disjoint G H) :
    Disjoint (G.neighborFinset x) (H.neighborFinset x) := by
  simp [← Finset.disjoint_coe, neighborSet_disjoint h]

end SimpleGraph

namespace SimpleGraph

open Finset

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

namespace EdgeLabeling

/-- The predicate `C.MonochromaticBetween X Y k` says every edge between `X` and `Y` is labelled
`k` by the labelling `C`. -/
def MonochromaticBetween (C : EdgeLabeling G K) (X Y : Set V) (k : K) : Prop :=
  ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ Y → (h : G.Adj x y) → C.get x y h = k

/-- `C.MonochromaticOf X k` says that every edge in `X` is labelled `k` by the labelling `C`. -/
def MonochromaticOf (C : EdgeLabeling G K) (X : Set V) (k : K) : Prop :=
  MonochromaticBetween C X X k

variable {W X Y Z : Set V} {k : K} {C : EdgeLabeling G K}

theorem monochromaticOf_iff_pairwise :
    C.MonochromaticOf X k ↔ X.Pairwise fun x y ↦ ∀ h : G.Adj x y, C.get x y h = k := by
  grind [MonochromaticOf, MonochromaticBetween, Set.Pairwise, Adj.ne]

lemma _root_.SimpleGraph.TopEdgeLabeling.monochromaticOf_iff_ne_of_adj {C : TopEdgeLabeling V K} :
    C.MonochromaticOf X k ↔ ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ X → (h : x ≠ y) → C.get x y h = k := by
  simp_rw [MonochromaticOf, MonochromaticBetween, top_adj]

namespace MonochromaticBetween

protected theorem symm (hXY : C.MonochromaticBetween X Y k) : C.MonochromaticBetween Y X k := by
  intro y hy x hx h
  rw [get_comm _ _ h]
  exact hXY hx hy _

protected theorem comm : C.MonochromaticBetween Y X k ↔ C.MonochromaticBetween X Y k :=
  ⟨.symm, .symm⟩

@[simp]
theorem empty_left : C.MonochromaticBetween ∅ Y k := by
  simp [MonochromaticBetween]

@[simp]
theorem empty_right : C.MonochromaticBetween X ∅ k := by
  simp [MonochromaticBetween]

theorem singleton_left {x : V} :
    C.MonochromaticBetween {x} Y k ↔ ∀ ⦃y⦄, y ∈ Y → (h : G.Adj x y) → C.get x y h = k := by
  simp [MonochromaticBetween]

theorem singleton_right {y : V} :
    C.MonochromaticBetween X {y} k ↔ ∀ ⦃x⦄, x ∈ X → (h : G.Adj x y) → C.get x y h = k := by
  simp [MonochromaticBetween]

theorem subsingleton_colours [Subsingleton K] : C.MonochromaticBetween X Y k :=
  fun _ _ _ _ _ ↦ Subsingleton.elim _ _

theorem union_left : C.MonochromaticBetween (X ∪ Y) Z k ↔
    C.MonochromaticBetween X Z k ∧ C.MonochromaticBetween Y Z k := by
  grind [MonochromaticBetween]

theorem union_right : C.MonochromaticBetween X (Y ∪ Z) k ↔
    C.MonochromaticBetween X Y k ∧ C.MonochromaticBetween X Z k := by
  grind [MonochromaticBetween]

protected theorem self : C.MonochromaticBetween X X k ↔ C.MonochromaticOf X k :=
  .rfl

protected theorem subset (hWX : C.MonochromaticBetween W X k) (hYW : Y ⊆ W) (hZX : Z ⊆ X) :
    C.MonochromaticBetween Y Z k :=
  fun _ hx _ hy ↦ hWX (hYW hx) (hZX hy)

protected theorem subset_left (hYZ : C.MonochromaticBetween Y Z k) (hXY : X ⊆ Y) :
    C.MonochromaticBetween X Z k :=
  hYZ.subset hXY (Set.Subset.refl Z)

protected theorem subset_right (hXZ : C.MonochromaticBetween X Z k) (hXY : Y ⊆ Z) :
    C.MonochromaticBetween X Y k :=
  hXZ.subset (Set.Subset.refl X) hXY

protected theorem image {C : EdgeLabeling G' K} {f : G ↪g G'}
    (hXY : (C.pullback f.toHom).MonochromaticBetween X Y k) :
    C.MonochromaticBetween (f '' X) (f '' Y) k := by
  simpa [MonochromaticBetween]

theorem compRight (h : C.MonochromaticBetween X Y k) (e : K → K') :
    (C.compRight e).MonochromaticBetween X Y (e k) := by
  intro x hx y hy h'
  rw [compRight_get, h hx hy h']

protected theorem injective (e : K → K') (he : Function.Injective e) :
    (C.compRight e).MonochromaticBetween X Y (e k) ↔ C.MonochromaticBetween X Y k := by
  simp_rw [EdgeLabeling.compRight, MonochromaticBetween, get_eq, Function.comp_apply, he.eq_iff]

end MonochromaticBetween

namespace MonochromaticOf

theorem subsingleton (hm : X.Subsingleton) : C.MonochromaticOf X k :=
  fun _ hx _ hy h ↦ (h.ne (hm hx hy)).elim

@[simp]
protected theorem empty : C.MonochromaticOf ∅ k :=
  .subsingleton Set.subsingleton_empty

@[simp]
protected theorem singleton {x : V} : C.MonochromaticOf {x} k :=
  .subsingleton Set.subsingleton_singleton

theorem subsingleton_colours [Subsingleton K] : C.MonochromaticOf X k :=
  MonochromaticBetween.subsingleton_colours

theorem compRight (h : C.MonochromaticOf X k) (e : K → K') :
    (C.compRight e).MonochromaticOf X (e k) :=
  MonochromaticBetween.compRight h e

protected theorem injective (e : K → K') (he : Function.Injective e) :
    (C.compRight e).MonochromaticOf X (e k) ↔ C.MonochromaticOf X k :=
  MonochromaticBetween.injective e he

theorem subset (hY : C.MonochromaticOf Y k) (hXY : X ⊆ Y) : C.MonochromaticOf X k :=
  MonochromaticBetween.subset hY hXY hXY

theorem image {C : EdgeLabeling G' K} {f : G ↪g G'} (h : (C.pullback f.toHom).MonochromaticOf X k) :
    C.MonochromaticOf (f '' X) k :=
  MonochromaticBetween.image h

protected theorem union : C.MonochromaticOf (X ∪ Y) k ↔
    C.MonochromaticOf X k ∧ C.MonochromaticOf Y k ∧ C.MonochromaticBetween X Y k := by
  grind [MonochromaticOf, MonochromaticBetween.union_left, MonochromaticBetween.comm]

protected theorem insert {x : V} :
    C.MonochromaticOf (insert x X) k ↔ C.MonochromaticOf X k ∧ C.MonochromaticBetween X {x} k := by
  simp [← Set.union_singleton, MonochromaticOf.union]

theorem image_top {C : TopEdgeLabeling V' K} {f : V ↪ V'}
    (h : (C.pullback f).MonochromaticOf X k) : C.MonochromaticOf (f '' X) k := by
  simpa [TopEdgeLabeling.monochromaticOf_iff_ne_of_adj]

theorem map_top {C : TopEdgeLabeling V' K} {f : V ↪ V'} {m : Finset V}
    (h : (C.pullback f).MonochromaticOf m k) : C.MonochromaticOf (m.map f) k := by
  rw [coe_map]
  exact h.image_top

end MonochromaticOf

end EdgeLabeling

section

variable {V V' K : Type*} (G : SimpleGraph V) {G' : SimpleGraph V'} (C : EdgeLabeling G' K) (c : K)

def LabelingContains : Prop :=
  G ⊑ C.labelGraph c -- should this be `∃ c`?

def LabelingIndContains : Prop :=
  G ⊴ C.labelGraph c

variable {G C c}

theorem LabelingIndContains.LabelingContains (h : G.LabelingIndContains C c) :
    G.LabelingContains C c :=
  h.isContained

end

section

-- todo: add two more general versions of `IsRamseyValid` for graphs in terms of `LabelingContains`
-- and `LabelingIndContains` but keep this def because it is needed to bootstrap existence of Ramsey
-- numbers for graphs.

/-- The predicate `IsRamseyValid V n` states that the type `V` is large enough to guarantee a
clique of size `n k` for some colour `k : K`. -/
def IsRamseyValid' (V : Type*) (n : K → ℕ) : Prop :=
  ∀ C : TopEdgeLabeling V K,
    ∃ (m : Finset V) (k : K), (⊤ : SimpleGraph V).LabelingContains C k ∧ n k ≤ m.card

/-- The predicate `IsRamseyValid N n` states that a complete graph of size `N` is large enough to
guarantee a clique of size `n k` for some colour `k : K`. -/
def IsRamseyValid'' (N : ℕ) (n : K → ℕ) : Prop :=
  ∀ C : TopEdgeLabeling (Fin N) K,
    ∃ (m : Finset V) (c : K), (⊤ : SimpleGraph V).LabelingContains C c ∧ n c ≤ m.card

end

end SimpleGraph












namespace Fin

open Function Matrix Fin
theorem update_vecCons_zero {α : Type*} {i : ℕ} {x y : α} {t : Fin i → α} :
    update (vecCons x t) 0 y = vecCons y t := by
  simp [vecCons]

theorem _root_.Function.update_cons_one {α : Type*} {i : ℕ} {x y z : α} {t : Fin i → α} :
    update (vecCons x (vecCons y t)) 1 z = vecCons x (vecCons z t) := by
  -- simp [vecCons]
  simp only [funext_iff, forall_fin_succ]
  refine ⟨rfl, rfl, fun j ↦ ?_⟩
  rw [update_of_ne]
  · simp only [vecCons, cons_succ]
  exact (succ_injective _).ne (Fin.succ_ne_zero _)

theorem _root_.Function.update_cons_two {α : Type*} {i : ℕ} {w x y z : α} {t : Fin i → α} :
    update (vecCons w (vecCons x (vecCons y t))) 2 z = vecCons w (vecCons x (vecCons z t)) := by
  simp only [funext_iff, forall_fin_succ]
  refine ⟨rfl, rfl, rfl, fun j ↦ ?_⟩
  rw [update_of_ne]
  · simp only [vecCons, cons_succ]
  exact (succ_injective _).ne ((succ_injective _).ne (succ_ne_zero _))

theorem _root_.Function.swap_cons {α : Type*} {i : ℕ} {x y : α} {t : Fin i → α} :
    vecCons x (vecCons y t) ∘ Equiv.swap 0 1 = vecCons y (vecCons x t) := by
  rw [funext_iff]
  simp only [forall_fin_succ]
  refine ⟨rfl, rfl, fun j ↦ ?_⟩
  simp only [vecCons, cons_succ, comp_apply]
  rw [Equiv.swap_apply_of_ne_of_ne, cons_succ, cons_succ]
  · exact succ_ne_zero _
  exact (succ_injective _).ne (succ_ne_zero _)

end Fin

open Finset
open Fintype (card)

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} {K K' : Type*}

section

theorem exists_even_degree [Fintype V] [DecidableRel G.Adj] (hV : Odd (card V)) :
    ∃ v : V, Even (G.degree v) := by
  have : (univ.filter (Odd <| G.degree ·)) ≠ univ := by
    rw [←card_lt_iff_ne_univ, (card_le_univ _).lt_iff_ne]
    intro h
    have h' := even_card_odd_degree_vertices G
    rw [h, ← Nat.not_odd_iff_even] at h'
    exact h' hV
  rw [Ne.eq_def, filter_eq_self] at this
  simpa using this

end

theorem TopEdgeLabeling.monochromaticOf_insert {C : TopEdgeLabeling V K} {c : K}
    {m : Set V} {x : V} (hx : x ∉ m) : C.MonochromaticOf (insert x m) c ↔
    C.MonochromaticOf m c ∧ ∀ ⦃y⦄, (H : y ∈ m) → C.get x y (H.ne_of_notMem hx).symm = c := by
  rw [Set.insert_eq, ← coe_singleton, Set.union_comm]
  convert EdgeLabeling.MonochromaticOf.union
  simp only [coe_singleton, EdgeLabeling.MonochromaticOf.singleton,
    EdgeLabeling.MonochromaticBetween, Set.mem_singleton_iff, top_adj, ne_eq, forall_eq, true_and]
  constructor
  · intros a y ym _
    rw [EdgeLabeling.get_comm]
    exact a ym
  · intros a y ym
    rw [EdgeLabeling.get_comm]
    exact a ym (ne_of_mem_of_not_mem ym hx)

theorem TopEdgeLabeling.Disjoint.monochromaticBetween {C : TopEdgeLabeling V K} {X Y : Set V}
    {k : K} (h : Disjoint X Y) : C.MonochromaticBetween X Y k ↔
      ∀ ⦃x⦄, (hx : x ∈ X) → ∀ ⦃y⦄, (hy : y ∈ Y) → C.get x y (h.ne_of_mem hx hy) = k :=
  forall₄_congr fun x hx y hy ↦ by simp [h.ne_of_mem hx hy]

open EdgeLabeling

variable {C : TopEdgeLabeling V K}

-- TODO (BM): I think the `∃` part of this should be its own def...
/-- The predicate `is_ramsey_valid V n` says that the type `V` is large enough to guarantee a
clique of size `n k` for some colour `k : K`.
-/
def IsRamseyValid (V : Type*) (n : K → ℕ) : Prop :=
  ∀ C : TopEdgeLabeling V K, ∃ (m : Finset V) (c : _), C.MonochromaticOf m c ∧ n c ≤ m.card

theorem IsRamseyValid.empty_colours [IsEmpty K] {n : K → ℕ} : IsRamseyValid (Fin 2) n := fun C ↦
  isEmptyElim (C.get 0 1 (by simp))

theorem IsRamseyValid.exists_zero_of_isEmpty [IsEmpty V] {n : K → ℕ} (h : IsRamseyValid V n) :
    ∃ c, n c = 0 :=
  let ⟨m, c, _, hc⟩ := h isEmptyElim
  ⟨c, by simpa [Subsingleton.elim m ∅] using hc⟩

theorem isRamseyValid_of_zero {n : K → ℕ} (c : K) (hc : n c = 0) : IsRamseyValid V n := fun C ↦
  ⟨∅, c, by simp, by simp [hc]⟩

theorem isRamseyValid_of_exists_zero (n : K → ℕ) (h : ∃ c, n c = 0) : IsRamseyValid V n :=
  let ⟨_, hc⟩ := h
  isRamseyValid_of_zero _ hc

theorem IsRamseyValid.mono_right {n n' : K → ℕ} (h : n ≤ n') (h' : IsRamseyValid V n') :
    IsRamseyValid V n := fun C ↦
  let ⟨m, c, hc, hm⟩ := h' C
  ⟨m, c, hc, hm.trans' (h _)⟩

theorem isRamseyValid_iff_eq {n : K → ℕ} :
    IsRamseyValid V n ↔
      ∀ C : TopEdgeLabeling V K, ∃ (m : Finset V) (c : K),
        C.MonochromaticOf m c ∧ n c = m.card := by
  refine forall_congr' fun C ↦ ?_
  rw [exists_comm, @exists_comm (Finset V)]
  refine exists_congr fun c ↦ ?_
  constructor
  · rintro ⟨a, ha, ha'⟩
    obtain ⟨b, hb, hb'⟩ := exists_subset_card_eq ha'
    exact ⟨b, ha.subset hb, hb'.symm⟩
  · rintro ⟨a, ha, ha'⟩
    exact ⟨_, ha, ha'.le⟩

theorem isRamseyValid_iff_embedding_aux {n : ℕ} (c : K) :
    (∃ m : Finset V, C.MonochromaticOf m c ∧ n = m.card) ↔
      Nonempty ((⊤ : SimpleGraph (Fin n)) ↪g C.labelGraph c) := by
  constructor
  · rintro ⟨m, hm, hm'⟩
    have : Fintype.card m = n := by rw [Fintype.card_coe, hm']
    classical
    obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq this
    refine ⟨⟨e.symm.toEmbedding.trans (Function.Embedding.subtype _), ?_⟩⟩
    intro a b
    simp only [Ne.eq_def, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Function.Embedding.coe_subtype, labelGraph_adj, top_adj, ← Subtype.ext_iff,
      EmbeddingLike.apply_eq_iff_eq]
    constructor
    · rintro ⟨h, -⟩
      exact h
    intro h
    exact ⟨h, hm (e.symm a).prop (e.symm b).prop _⟩
  rintro ⟨f⟩
  refine ⟨(univ : Finset (Fin n)).map f.toEmbedding, ?_, ?_⟩
  · rw [TopEdgeLabeling.monochromaticOf_iff_ne_of_adj]
    simp only [Ne.eq_def, RelEmbedding.inj, coe_map, RelEmbedding.coe_toEmbedding, Set.mem_image,
      coe_univ, Set.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro x y h
    have : (⊤ : SimpleGraph (Fin n)).Adj x y := h
    simpa [-top_adj, ←f.map_rel_iff, h, RelEmbedding.inj] using this
      -- this simpa needs more help than in lean 3
  rw [card_map, card_fin]

-- BM: pretty good chance this is a better definition...
-- it also generalises better to induced ramsey numbers of graphs
-- and if you transfer with `top_hom_graph_equiv` you get ramsey numbers of graphs
theorem isRamseyValid_iff_embedding {n : K → ℕ} :
    IsRamseyValid V n ↔
      ∀ C : TopEdgeLabeling V K,
        ∃ c : K, Nonempty ((⊤ : SimpleGraph (Fin (n c))) ↪g C.labelGraph c) := by
  rw [isRamseyValid_iff_eq]
  refine forall_congr' fun C ↦ ?_
  rw [exists_comm]
  simp only [isRamseyValid_iff_embedding_aux]

theorem IsRamseyValid.embedding {n : K → ℕ} (f : V ↪ V') (h' : IsRamseyValid V n) :
    IsRamseyValid V' n := fun C ↦
  let ⟨m', c, hc, hm'⟩ := h' (C.pullback f)
  ⟨m'.map f, c, by simpa only [coe_map] using hc.image_top, hm'.trans_eq (card_map _).symm⟩

theorem IsRamseyValid.card_fin [Fintype V] {N : ℕ} {n : K → ℕ} (h : N ≤ card V)
    (h' : IsRamseyValid (Fin N) n) : IsRamseyValid V n :=
  h'.embedding <| (Fin.castLEOrderEmb h).toEmbedding.trans (Fintype.equivFin V).symm

theorem IsRamseyValid.equiv_left (n : K → ℕ) (f : V ≃ V') :
    IsRamseyValid V n ↔ IsRamseyValid V' n :=
  ⟨fun h ↦ h.embedding f, fun h ↦ h.embedding f.symm⟩

theorem IsRamseyValid.equiv_right {n : K → ℕ} (f : K' ≃ K) (h : IsRamseyValid V n) :
    IsRamseyValid V (n ∘ f) := fun C ↦
  let ⟨m, c, hm, hc⟩ := h (C.compRight f)
  ⟨m, f.symm c, by rwa [← MonochromaticOf.injective f f.injective, f.apply_symm_apply], by
    simpa using hc⟩

theorem isRamseyValid_equiv_right {n : K → ℕ} (f : K' ≃ K) :
    IsRamseyValid V (n ∘ f) ↔ IsRamseyValid V n :=
  ⟨fun h ↦ by convert h.equiv_right f.symm; ext; simp, fun h ↦ h.equiv_right _⟩

instance [DecidableEq K] [DecidableEq V] [DecidableRel G.Adj] (C : EdgeLabeling G K) (m : Finset V)
    (c : K) : Decidable (C.MonochromaticOf m c) :=
  decidable_of_iff' _ C.monochromaticOf_iff_pairwise

instance [DecidableEq K] [Fintype K] [DecidableEq V] [Fintype V] (n : K → ℕ) :
    Decidable (IsRamseyValid V n) :=
  Fintype.decidableForallFintype

theorem ramsey_base [Nonempty V] {n : K → ℕ} (hn : ∃ k, n k ≤ 1) : IsRamseyValid V n :=
  by
  inhabit V
  obtain ⟨k, hk⟩ := hn
  exact fun C ↦ ⟨{default}, k, by simpa using hk⟩

theorem ramsey_base' [Fintype V] (n : K → ℕ) (hn : ∃ k, n k ≤ 1) (hV : 1 ≤ card V) :
    IsRamseyValid V n :=
  @ramsey_base _ _ (Fintype.card_pos_iff.1 hV) _ hn

theorem isRamseyValid_min [Fintype V] [Nonempty K] {n : K → ℕ} {n' : ℕ} (h : IsRamseyValid V n)
    (hn : ∀ k, n' ≤ n k) : n' ≤ card V :=
  let ⟨m, _, _, hm⟩ := h (Classical.arbitrary (TopEdgeLabeling V K))
  (hn _).trans (hm.trans (Finset.card_le_univ m))

theorem isRamseyValid_unique [Fintype V] [Unique K] {n : K → ℕ} (hV : n default ≤ card V) :
    IsRamseyValid V n := fun C ↦ ⟨univ, default, MonochromaticOf.subsingleton_colours, by simpa⟩

theorem IsRamseyValid.remove_twos {n : K → ℕ} (h : IsRamseyValid V n) :
    IsRamseyValid V fun k : { k : K // n k ≠ 2 } ↦ n k := by
  cases isEmpty_or_nonempty V
  · obtain ⟨c, hc⟩ := h.exists_zero_of_isEmpty
    exact isRamseyValid_of_zero ⟨c, by simp [hc]⟩ hc
  by_cases h' : ∃ k, n k ≤ 1
  · obtain ⟨k, hk⟩ := h'
    refine ramsey_base ⟨⟨k, ?_⟩, hk⟩
    grind
  simp only [not_exists, not_le, Nat.lt_iff_add_one_le] at h'
  intro C
  obtain ⟨m, c, hm, hc⟩ := h (C.compRight Subtype.val)
  have : 1 < m.card := (h' c).trans hc
  rw [Finset.one_lt_card_iff] at this
  obtain ⟨a, b, ha, hb, hab⟩ := this
  have : Subtype.val (C.get a b hab) = c := hm ha hb hab
  refine ⟨m, _, ?_, hc.trans_eq' (congr_arg n this.symm)⟩
  rwa [← MonochromaticOf.injective _ Subtype.val_injective, this]

theorem IsRamseyValid.of_remove_twos {n : K → ℕ}
    (h : IsRamseyValid V fun k : { k : K // n k ≠ 2 } ↦ n k) : IsRamseyValid V n :=
  by
  intro C
  classical
  by_cases h'' : ∃ (x y : V) (H : x ≠ y), n (C.get x y H) = 2
  · obtain ⟨x, y, H, hxy⟩ := h''
    refine ⟨({x, y} : Finset V), C.get x y H, ?_, ?_⟩
    · rw [coe_pair, MonochromaticOf.insert]
      refine ⟨MonochromaticOf.singleton, ?_⟩
      simp only [MonochromaticBetween, Set.mem_singleton_iff, top_adj, ne_eq, forall_eq]
      exact fun _ ↦ get_comm x y _
    rw [hxy, card_pair H]
  push Not at h''
  let C' : TopEdgeLabeling V { k : K // n k ≠ 2 } :=
    EdgeLabeling.mk (fun x y h ↦ ⟨C.get x y h, h'' _ _ h⟩) ?_
  swap
  · intro x y h
    ext
    dsimp
    exact get_comm _ _ _
  obtain ⟨m, c, hm, hc⟩ := h C'
  refine ⟨m, c, ?_, hc⟩
  intro x hx y hy h
  exact Subtype.ext_iff.1 (hm hx hy h)

theorem isRamseyValid_iff_remove_twos (n : K → ℕ) :
    (IsRamseyValid V fun k : { k : K // n k ≠ 2 } ↦ n k) ↔ IsRamseyValid V n :=
  ⟨IsRamseyValid.of_remove_twos, IsRamseyValid.remove_twos⟩

theorem isRamseyValid_two {n : K → ℕ} {n' : K' → ℕ} (f : K' → K)
    (hf : ∀ x : K', n' x ≠ 2 → n (f x) ≠ 2)
    (hf_inj : ∀ x y : K', n' x ≠ 2 → n' y ≠ 2 → f x = f y → x = y)
    (hf_surj : ∀ x : K, n x ≠ 2 → ∃ y : K', n' y ≠ 2 ∧ f y = x)
    (hf_comm : ∀ x : K', n' x ≠ 2 → n (f x) = n' x) : IsRamseyValid V n' ↔ IsRamseyValid V n :=
  by
  let e : { k // n' k ≠ 2 } → { k // n k ≠ 2 } := fun k ↦ ⟨f k, hf _ k.prop⟩
  have he : Function.Injective e := fun a b h ↦
    Subtype.ext (hf_inj _ _ a.prop b.prop (Subtype.ext_iff.1 h))
  have he' : Function.Surjective e := by
    rintro ⟨i, hi⟩
    simpa [e] using hf_surj i hi
  rw [← isRamseyValid_iff_remove_twos n, ← isRamseyValid_iff_remove_twos n', ←
    isRamseyValid_equiv_right (Equiv.ofBijective e ⟨he, he'⟩)]
  congr! 2 with ⟨k, hk⟩
  exact (hf_comm _ hk).symm

open scoped BigOperators

variable [DecidableEq K'] [Fintype K'] {n : K → ℕ}

theorem ramsey_fin_induct_aux {V : Type*} [DecidableEq K] {n : K → ℕ} (N : K → ℕ)
    {C : TopEdgeLabeling V K} (m : K → Finset V) (x : V)
    (hN : ∀ k, IsRamseyValid (Fin (N k)) (Function.update n k (n k - 1))) (hx : ∀ k, x ∉ m k)
    (h : ∃ k, N k ≤ (m k).card)
    (hm : ∀ (k) (y : V) (hy : y ∈ m k), C.get x y (ne_of_mem_of_not_mem hy (hx k)).symm = k) :
    ∃ (m : Finset V) (c : _), C.MonochromaticOf m c ∧ n c ≤ m.card := by
  classical
  obtain ⟨k, hk⟩ := h
  have : IsRamseyValid (m k) (Function.update n k (n k - 1)) := (hN k).card_fin (by simp [hk])
  obtain ⟨m', k', hm', hk'⟩ := this (C.pullback (Function.Embedding.subtype _))
  rcases ne_or_eq k k' with (hk | rfl)
  · exact ⟨_, _, hm'.map_top, by simpa [hk.symm] using hk'⟩
  refine ⟨insert (x : V) (m'.map (Function.Embedding.subtype _)), k, ?_, ?_⟩
  · rw [coe_insert, MonochromaticOf.insert]
    refine ⟨hm'.map_top, ?_⟩
    simp only [MonochromaticBetween, coe_map, Function.Embedding.subtype_apply, Set.mem_image,
      mem_coe, Subtype.exists, exists_and_right, exists_eq_right, Set.mem_singleton_iff, top_adj,
      ne_eq, forall_eq, forall_exists_index]
    intros y ym _ _
    rw [get_comm]
    exact hm k y ym
  have : x ∉ (m'.map (Function.Embedding.subtype _) : Set V) := by simp [hx k]
  rw [card_insert_of_notMem this, card_map, ← tsub_le_iff_right]
  rwa [Function.update_self] at hk'

theorem ramsey_fin_induct [DecidableEq K] [Fintype K] (n : K → ℕ) (N : K → ℕ)
    (hN : ∀ k, IsRamseyValid (Fin (N k)) (Function.update n k (n k - 1))) :
    IsRamseyValid (Fin (∑ k, (N k - 1) + 2)) n := by
  by_cases h : ∃ k, n k ≤ 1
  · refine ramsey_base' _ h ?_
    rw [Fintype.card_fin]
    exact (Nat.le_add_left _ _).trans' (by grind)
  push Not at h
  have hN' : ∀ k, 1 ≤ N k := by
    intro k
    by_contra!
    have : IsEmpty (Fin (N k)) :=
      by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]
      simpa only [Nat.lt_one_iff] using this
    obtain ⟨k', hk'⟩ := (hN k).exists_zero_of_isEmpty
    rcases eq_or_ne k k' with (rfl | hk)
    · simp only [Function.update_self, tsub_eq_zero_iff_le] at hk'
      exact hk'.not_gt (h _)
    rw [Function.update_of_ne hk.symm] at hk'
    simpa only [not_lt_zero] using (h k').trans_eq hk'
  classical
  set V := Fin (∑ k, (N k - 1) + 2)
  intro C
  let x : V := 0
  let m : K → Finset V := fun k ↦ neighborFinset (C.labelGraph k) x
  have : univ.biUnion m = {x}ᶜ := by
    simp only [← Finset.coe_inj, coe_biUnion, mem_coe, mem_univ, Set.iUnion_true, coe_compl,
      coe_singleton, coe_neighborFinset, m]
    rw [← neighborSet_iSup, EdgeLabeling.iSup_labelGraph C, neighborSet_top]
  have e : ∑ k, (m k).card = ∑ k, (N k - 1) + 1 :=
    by
    rw [← card_biUnion, this, card_compl, ← card_univ, card_fin, card_singleton,
      Nat.add_succ_sub_one]
    rintro x _ y _ h
    refine neighborFinset_disjoint ?_
    exact EdgeLabeling.pairwiseDisjoint_univ_labelGraph (by simp) (by simp) h
  have : ∃ k, N k - 1 < (m k).card := by
    by_contra!
    have : ∑ k, (m k).card ≤ ∑ k, (N k - 1) := sum_le_sum fun k _ ↦ this k
    rw [e] at this
    simp only [add_le_iff_nonpos_right, le_zero_iff, Nat.one_ne_zero] at this
  obtain ⟨k, hk⟩ := this
  rw [tsub_lt_iff_right (hN' _), Nat.lt_add_one_iff] at hk
  refine ramsey_fin_induct_aux _ m x hN ?_ ⟨k, hk⟩ ?_
  · simp [m]
  · simp [m]

theorem ramsey_fin_exists [Finite K] (n : K → ℕ) : ∃ N, IsRamseyValid (Fin N) n := by
  classical
  refine @WellFoundedLT.induction _ _ _ (fun a ↦ ∃ N, IsRamseyValid (Fin N) a) n ?_
  clear n
  intro n ih
  by_cases h : ∃ k, n k = 0
  · exact ⟨0, isRamseyValid_of_exists_zero _ h⟩
  push Not at h
  have : ∀ k, Function.update n k (n k - 1) < n :=
    by
    simp only [update_lt_self_iff]
    intro k
    exact Nat.pred_lt (h k)
  have := fun k ↦ ih _ (this k)
  choose N hN using this
  cases nonempty_fintype K
  exact ⟨_, ramsey_fin_induct _ _ hN⟩

-- hn can be weakened but it's just a nontriviality assumption
theorem ramsey_fin_induct' [DecidableEq K] [Fintype K] (n : K → ℕ) (N : K → ℕ) (hn : ∀ k, 2 ≤ n k)
    (hN : ∀ k, IsRamseyValid (Fin (N k)) (Function.update n k (n k - 1))) :
    IsRamseyValid (Fin (∑ k, N k + 2 - card K)) n := by
  have hN' : ∀ k, 1 ≤ N k := by
    intro k
    by_contra!
    have : IsEmpty (Fin (N k)) :=
      by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]
      simpa only [Nat.lt_one_iff] using this
    obtain ⟨k', hk'⟩ := (hN k).exists_zero_of_isEmpty
    rcases eq_or_ne k k' with (rfl | hk)
    · simp only [Function.update_self, tsub_eq_zero_iff_le] at hk'
      exact hk'.not_gt (hn _)
    rw [Function.update_of_ne hk.symm] at hk'
    simpa only [nonpos_iff_eq_zero, OfNat.ofNat_ne_zero] using (hn k').trans_eq hk'
  have h : ∀ x : K, x ∈ (univ : Finset K) → 1 ≤ N x := by simpa using hN'
  have := ramsey_fin_induct n N hN
  rwa [sum_tsub_distrib _ h, tsub_add_eq_add_tsub, ← Fintype.card_eq_sum_ones] at this
  exact sum_le_sum h

open Matrix (vecCons)

theorem ramsey_fin_induct_two {i j Ni Nj : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hi' : IsRamseyValid (Fin Ni) ![i - 1, j]) (hj' : IsRamseyValid (Fin Nj) ![i, j - 1]) :
    IsRamseyValid (Fin (Ni + Nj)) ![i, j] := by
  classical
  have : ∑ z : Fin 2, ![Ni, Nj] z + 2 - card (Fin 2) = Ni + Nj := by simp
  have h := ramsey_fin_induct' ![i, j] ![Ni, Nj] ?_ ?_
  · rwa [this] at h
  · rw [Fin.forall_fin_two]
    exact ⟨hi, hj⟩
  · rw [Fin.forall_fin_two]
    simp [Fin.update_vecCons_zero, Function.update_cons_one, hi', hj']

theorem ramsey_fin_induct_two_evens {i j Ni Nj : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hNi : Even Ni)
    (hNj : Even Nj) (hi' : IsRamseyValid (Fin Ni) ![i - 1, j])
    (hj' : IsRamseyValid (Fin Nj) ![i, j - 1]) : IsRamseyValid (Fin (Ni + Nj - 1)) ![i, j] := by
  have hNi' : 1 ≤ Ni := by
    by_contra!
    have : IsEmpty (Fin Ni) :=
      by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]
      simpa only [Nat.lt_one_iff] using this
    obtain ⟨k', hk'⟩ := hi'.exists_zero_of_isEmpty
    revert k'
    simp only [Fin.forall_fin_two, imp_false, Matrix.cons_val_zero, tsub_eq_zero_iff_le, not_le,
      Matrix.cons_val_one]
    exact ⟨hi, by grind⟩
  have hNj' : 1 ≤ Nj := by
    by_contra!
    have : IsEmpty (Fin Nj) :=
      by
      rw [← Fintype.card_eq_zero_iff, Fintype.card_fin]
      simpa only [Nat.lt_one_iff] using this
    obtain ⟨k', hk'⟩ := hj'.exists_zero_of_isEmpty
    revert k'
    simp only [Fin.forall_fin_two, imp_false, Matrix.cons_val_zero, tsub_eq_zero_iff_le, not_le,
      Matrix.cons_val_one]
    exact ⟨by grind, hj⟩
  have : Odd (card (Fin (Ni + Nj - 1))) :=
    by
    rw [Fintype.card_fin, Nat.odd_sub (le_add_right hNi')]
    simp [hNi, hNj, parity_simps]
  intro C
  obtain ⟨x, hx⟩ := @exists_even_degree (Fin (Ni + Nj - 1)) (C.labelGraph 0) _ _ this
  let m : Fin 2 → Finset (Fin (Ni + Nj - 1)) := fun k ↦ neighborFinset (C.labelGraph k) x
  change Even (m 0).card at hx
  have : univ.biUnion m = {x}ᶜ :=
    by
    simp only [← Finset.coe_inj, coe_biUnion, mem_coe, mem_univ, Set.iUnion_true, coe_compl,
      coe_singleton, m, coe_neighborFinset]
    rw [← neighborSet_iSup, EdgeLabeling.iSup_labelGraph C, neighborSet_top]
  have e : ∑ k, (m k).card = Ni + Nj - 2 :=
    by
    rw [← card_biUnion, this, card_compl, ← card_univ, card_fin, card_singleton, Nat.sub_sub]
    rintro x _ y _ h
    refine neighborFinset_disjoint ?_
    exact EdgeLabeling.pairwiseDisjoint_univ_labelGraph (by simp) (by simp) h
  have : Ni ≤ (m 0).card ∨ Nj ≤ (m 1).card :=
    by
    have : (m 0).card + 1 ≠ Ni := by
      intro h
      rw [← h] at hNi
        -- regression (maybe temporary): this extra simp is a weirdness with Lean 4 simp/zeta
      simp [hx, parity_simps] at hNi
    rw [eq_tsub_iff_add_eq_of_le (add_le_add hNi' hNj'), Fin.sum_univ_two] at e
    by_contra! h'
    rw [Nat.lt_iff_add_one_le, Nat.lt_iff_add_one_le, le_iff_lt_or_eq, or_iff_left this,
      Nat.lt_iff_add_one_le, add_assoc] at h'
    have := add_le_add h'.1 h'.2
    rw [add_add_add_comm, ← add_assoc, e] at this
    simp only [add_le_iff_nonpos_right, le_zero_iff, Nat.one_ne_zero] at this
  refine ramsey_fin_induct_aux ![Ni, Nj] m x ?_ (by simp [m]) ?_ ?_
  · rw [Fin.forall_fin_two, Fin.update_vecCons_zero, Function.update_cons_one]
    exact ⟨hi', hj'⟩
  · rwa [Fin.exists_fin_two]
  · rw [Fin.forall_fin_two]
    simp [m]

theorem ramsey_fin_induct_three {i j k Ni Nj Nk : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hk : 2 ≤ k)
    (hi' : IsRamseyValid (Fin Ni) ![i - 1, j, k]) (hj' : IsRamseyValid (Fin Nj) ![i, j - 1, k])
    (hk' : IsRamseyValid (Fin Nk) ![i, j, k - 1]) :
    IsRamseyValid (Fin (Ni + Nj + Nk - 1)) ![i, j, k] := by
  have : ∑ k : Fin 3, ![Ni, Nj, Nk] k + 2 - card (Fin 3) = Ni + Nj + Nk - 1 := by
    rw [Fintype.card_fin, Nat.succ_sub_succ_eq_sub, Fin.sum_univ_three]
    rfl
  have h := ramsey_fin_induct' ![i, j, k] ![Ni, Nj, Nk] ?_ ?_
  · rwa [this] at h
  · rw [Fin.forall_fin_succ, Fin.forall_fin_two]
    exact ⟨hi, hj, hk⟩
  · rw [Fin.forall_fin_succ, Fin.forall_fin_two, Fin.update_vecCons_zero, Fin.succ_zero_eq_one,
      Fin.succ_one_eq_two, Function.update_cons_one, Function.update_cons_two]
    exact ⟨hi', hj', hk'⟩

variable {N : ℕ} [Fintype V] [DecidableEq K] [Fintype K]

/-- Given a tuple `n : K → ℕ` of naturals indexed by `K`, define the ramsey number as the smallest
`N` such that any labelling of the complete graph on `N` vertices with `K` labels contains a
subset of size `n k` in which every edge is labelled `k`.
While this definition is computable, it is not at all efficient to compute.
-/
def ramseyNumber (n : K → ℕ) : ℕ :=
  Nat.find (ramsey_fin_exists n)

theorem ramseyNumber_spec_fin (n : K → ℕ) : IsRamseyValid (Fin (ramseyNumber n)) n :=
  Nat.find_spec (ramsey_fin_exists n)

theorem ramseyNumber_spec (h : ramseyNumber n ≤ card V) : IsRamseyValid V n :=
  (ramseyNumber_spec_fin n).card_fin h

theorem ramseyNumber_min_fin (hN : IsRamseyValid (Fin N) n) : ramseyNumber n ≤ N :=
  Nat.find_min' (ramsey_fin_exists n) hN

theorem ramseyNumber_min (hN : IsRamseyValid V n) : ramseyNumber n ≤ card V :=
  ramseyNumber_min_fin (hN.embedding (Fintype.equivFin V).toEmbedding)

theorem ramseyNumber_le_iff : ramseyNumber n ≤ card V ↔ IsRamseyValid V n :=
  ⟨ramseyNumber_spec, ramseyNumber_min⟩

theorem ramseyNumber_le_iff_fin : ramseyNumber n ≤ N ↔ IsRamseyValid (Fin N) n :=
  ⟨fun h ↦ (ramseyNumber_spec_fin n).embedding (Fin.castLEOrderEmb h).toEmbedding,
   ramseyNumber_min_fin⟩

theorem ramseyNumber_eq_of (h : IsRamseyValid (Fin (N + 1)) n) (h' : ¬IsRamseyValid (Fin N) n) :
    ramseyNumber n = N + 1 := by
  rw [← ramseyNumber_le_iff_fin] at h h';
  exact h.antisymm (lt_of_not_ge h')

theorem ramseyNumber_congr {n' : K' → ℕ}
    (h : ∀ N, IsRamseyValid (Fin N) n ↔ IsRamseyValid (Fin N) n') :
    ramseyNumber n = ramseyNumber n' :=
  (ramseyNumber_min_fin ((h _).2 (ramseyNumber_spec_fin _))).antisymm
    (ramseyNumber_min_fin ((h _).1 (ramseyNumber_spec_fin _)))

theorem ramseyNumber_equiv (f : K' ≃ K) : ramseyNumber (n ∘ f) = ramseyNumber n :=
  ramseyNumber_congr fun _ ↦ isRamseyValid_equiv_right f

theorem ramseyNumber_first_swap {i : ℕ} (x y : ℕ) (t : Fin i → ℕ) :
    ramseyNumber (vecCons x (vecCons y t)) = ramseyNumber (vecCons y (vecCons x t)) := by
  have : vecCons x (vecCons y t) ∘ Equiv.swap 0 1 = vecCons y (vecCons x t) := by
    rw [Function.swap_cons]
  rw [← this, ramseyNumber_equiv]

theorem ramseyNumber_pair_swap (x y : ℕ) : ramseyNumber ![x, y] = ramseyNumber ![y, x] :=
  ramseyNumber_first_swap _ _ _

theorem ramseyNumber.eq_zero_iff : ramseyNumber n = 0 ↔ ∃ c, n c = 0 := by
  rw [← le_zero_iff, ramseyNumber_le_iff_fin]
  exact ⟨fun h ↦ h.exists_zero_of_isEmpty, isRamseyValid_of_exists_zero _⟩

theorem ramseyNumber.exists_zero_of_eq_zero (h : ramseyNumber n = 0) : ∃ c, n c = 0 :=
  ramseyNumber.eq_zero_iff.1 h

theorem ramseyNumber_exists_zero (c : K) (hc : n c = 0) : ramseyNumber n = 0 :=
  ramseyNumber.eq_zero_iff.2 ⟨c, hc⟩

theorem ramseyNumber_pos : 0 < ramseyNumber n ↔ ∀ c, n c ≠ 0 := by
  rw [pos_iff_ne_zero, Ne.eq_def, ramseyNumber.eq_zero_iff, not_exists]

theorem ramseyNumber_le_one (hc : ∃ c, n c ≤ 1) : ramseyNumber n ≤ 1 := by
  rw [ramseyNumber_le_iff_fin]; exact ramsey_base hc

theorem ramseyNumber_ge_min [Nonempty K] (i : ℕ) (hk : ∀ k, i ≤ n k) : i ≤ ramseyNumber n :=
  (isRamseyValid_min (ramseyNumber_spec_fin n) hk).trans_eq (card_fin _)

theorem exists_le_of_ramseyNumber_le [Nonempty K] (i : ℕ) (hi : ramseyNumber n ≤ i) :
    ∃ k, n k ≤ i := by contrapose! hi; exact ramseyNumber_ge_min (i + 1) hi

instance [Subsingleton V] : IsEmpty (edgeSet G) := by
  constructor
  rintro ⟨i, hi⟩
  induction i using Sym2.inductionOn
  simp only [mem_edgeSet] at hi
  cases hi.ne (Subsingleton.elim _ _)

instance [Subsingleton V] : Unique (EdgeLabeling G K) := by
  exact Pi.uniqueOfIsEmpty _

@[simp]
theorem ramseyNumber_empty [IsEmpty K] : ramseyNumber n = 2 := by
  refine ramseyNumber_eq_of ?_ ?_
  · exact IsRamseyValid.empty_colours
  simp [IsRamseyValid]

theorem ramseyNumber_nil : ramseyNumber ![] = 2 :=
  ramseyNumber_empty

theorem exists_le_one_of_ramseyNumber_le_one (hi : ramseyNumber n ≤ 1) : ∃ k, n k ≤ 1 :=
  haveI : Nonempty K := by
    rw [← not_isEmpty_iff]
    intro
    rw [ramseyNumber_empty] at hi
    grind
  exists_le_of_ramseyNumber_le _ hi

theorem ramseyNumber_eq_one (hc : ∃ c, n c = 1) (hc' : ∀ c, n c ≠ 0) : ramseyNumber n = 1 := by
  obtain ⟨c, hc⟩ := hc
  refine (ramseyNumber_le_one ⟨c, hc.le⟩).antisymm ?_
  rwa [Nat.succ_le_iff, ramseyNumber_pos]

theorem ramseyNumber_eq_one_iff : ((∃ c, n c = 1) ∧ ∀ c, n c ≠ 0) ↔ ramseyNumber n = 1 := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ramseyNumber_eq_one h₁ h₂
  intro h
  have : ramseyNumber n ≠ 0 := by rw [h]; simp
  rw [Ne.eq_def, ramseyNumber.eq_zero_iff, not_exists] at this
  obtain ⟨k, hk⟩ := exists_le_one_of_ramseyNumber_le_one h.le
  refine ⟨⟨k, hk.antisymm ?_⟩, this⟩
  rw [Nat.succ_le_iff, pos_iff_ne_zero]
  exact this _

theorem ramseyNumber_unique_colour [Unique K] : ramseyNumber n = n default :=
  by
  refine le_antisymm (ramseyNumber_min_fin (isRamseyValid_unique (by simp))) ?_
  refine ramseyNumber_ge_min _ fun k ↦ ?_
  rw [Subsingleton.elim default k]

@[simp]
theorem ramseyNumber_singleton {i : ℕ} : ramseyNumber ![i] = i := by
  rw [ramseyNumber_unique_colour, Matrix.cons_val_fin_one]

theorem ramseyNumber.mono {n n' : K → ℕ} (h : n ≤ n') : ramseyNumber n ≤ ramseyNumber n' := by
  rw [ramseyNumber_le_iff_fin]; exact (ramseyNumber_spec_fin _).mono_right h

theorem ramseyNumber.mono_two {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    ramseyNumber ![a, c] ≤ ramseyNumber ![b, d] :=
  ramseyNumber.mono (by rw [Pi.le_def, Fin.forall_fin_two]; exact ⟨hab, hcd⟩)

theorem ramseyNumber_monotone {i : ℕ} : Monotone (ramseyNumber : (Fin i → ℕ) → ℕ) := fun _ _ h ↦
  ramseyNumber.mono h

theorem ramseyNumber_remove_two {n : K → ℕ} {n' : K' → ℕ} (f : K' → K)
    (hf : ∀ x : K', n' x ≠ 2 → n (f x) ≠ 2)
    (hf_inj : ∀ x y : K', n' x ≠ 2 → n' y ≠ 2 → f x = f y → x = y)
    (hf_surj : ∀ x : K, n x ≠ 2 → ∃ y : K', n' y ≠ 2 ∧ f y = x)
    (hf_comm : ∀ x : K', n' x ≠ 2 → n (f x) = n' x) : ramseyNumber n' = ramseyNumber n :=
  ramseyNumber_congr fun _ ↦ isRamseyValid_two f hf hf_inj hf_surj hf_comm

@[simp]
theorem ramseyNumber_cons_two {i : ℕ} {n : Fin i → ℕ} :
    ramseyNumber (Matrix.vecCons 2 n) = ramseyNumber n := by
  refine (ramseyNumber_remove_two Fin.succ ?_ ?_ ?_ ?_).symm <;> simp [Fin.forall_fin_succ]

@[simp]
theorem ramseyNumber_cons_zero {i : ℕ} {n : Fin i → ℕ} : ramseyNumber (Matrix.vecCons 0 n) = 0 :=
  ramseyNumber_exists_zero 0 (by simp)

theorem ramseyNumber_cons_one_of_one_le {i : ℕ} {n : Fin i → ℕ} (h : ∀ k, n k ≠ 0) :
    ramseyNumber (Matrix.vecCons 1 n) = 1 :=
  by
  refine ramseyNumber_eq_one ⟨0, rfl⟩ ?_
  rw [Fin.forall_fin_succ]
  simpa using h

theorem ramseyNumber_one_succ {i : ℕ} : ramseyNumber ![1, i + 1] = 1 :=
  ramseyNumber_cons_one_of_one_le (by simp)

theorem ramseyNumber_succ_one {i : ℕ} : ramseyNumber ![i + 1, 1] = 1 := by
  rw [ramseyNumber_pair_swap, ramseyNumber_one_succ]

theorem ramseyNumber_two_left {i : ℕ} : ramseyNumber ![2, i] = i := by simp

@[simp]
theorem ramseyNumber_two_right {i : ℕ} : ramseyNumber ![i, 2] = i := by
  rw [ramseyNumber_pair_swap, ramseyNumber_two_left]

-- if the condition `h` fails, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
theorem ramseyNumber_multicolour_bound (h : ∀ k, 2 ≤ n k) :
    ramseyNumber n ≤ ∑ k, ramseyNumber (Function.update n k (n k - 1)) + 2 - card K :=
  by
  rw [ramseyNumber_le_iff_fin]
  exact ramsey_fin_induct' _ _ h fun k ↦ ramseyNumber_spec_fin _

-- if the conditions `hi` or `hj` fail, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
theorem ramseyNumber_two_colour_bound_aux {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
    ramseyNumber ![i, j] ≤ ramseyNumber ![i - 1, j] + ramseyNumber ![i, j - 1] :=
  by
  rw [ramseyNumber_le_iff_fin]
  refine ramsey_fin_induct_two hi hj ?_ ?_ <;> exact ramseyNumber_spec_fin _

theorem ramseyNumber_two_colour_bound (i j : ℕ) (hij : i ≠ 1 ∨ j ≠ 1) :
    ramseyNumber ![i, j] ≤ ramseyNumber ![i - 1, j] + ramseyNumber ![i, j - 1] :=
  by
  wlog h : i ≤ j generalizing i j
  · refine (ramseyNumber_pair_swap _ _).trans_le ((this _ _ hij.symm (le_of_not_ge h)).trans ?_)
    rw [ramseyNumber_pair_swap, add_comm, add_le_add_iff_right, ramseyNumber_pair_swap]
  rcases i with (_ | _ | i)
  · simp
  · rcases j with (_ | _ | _)
    · simp
    · simp at hij
    rw [ramseyNumber_one_succ, Nat.sub_self, ramseyNumber_cons_zero, zero_add,
      Nat.succ_sub_succ_eq_sub, Nat.sub_zero, ramseyNumber_one_succ]
  have : 2 ≤ i + 2 := by simp
  exact ramseyNumber_two_colour_bound_aux this (this.trans h)

-- a slightly odd shaped bound to make it more practical for explicit computations
theorem ramseyNumber_two_colour_bound_even {i j} (Ni Nj : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (hNi : ramseyNumber ![i - 1, j] ≤ Ni) (hNj : ramseyNumber ![i, j - 1] ≤ Nj) (hNi' : Even Ni)
    (hNj' : Even Nj) : ramseyNumber ![i, j] ≤ Ni + Nj - 1 := by
  rw [ramseyNumber_le_iff_fin] at hNi hNj ⊢
  exact ramsey_fin_induct_two_evens hi hj hNi' hNj' hNi hNj

-- if the conditions `hi`, `hj` or `hk` fail, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
theorem ramseyNumber_three_colour_bound {i j k : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hk : 2 ≤ k) :
    ramseyNumber ![i, j, k] ≤
      ramseyNumber ![i - 1, j, k] + ramseyNumber ![i, j - 1, k] + ramseyNumber ![i, j, k - 1] - 1 :=
  by
  rw [ramseyNumber_le_iff_fin]
  refine ramsey_fin_induct_three hi hj hk ?_ ?_ ?_ <;> exact ramseyNumber_spec_fin _

/-- The diagonal ramsey number, defined by R(k, k). -/
def diagonalRamsey (k : ℕ) : ℕ :=
  ramseyNumber ![k, k]

theorem diagonalRamsey.def {k : ℕ} : diagonalRamsey k = ramseyNumber ![k, k] :=
  rfl

@[simp]
theorem diagonalRamsey_zero : diagonalRamsey 0 = 0 :=
  ramseyNumber_cons_zero

@[simp]
theorem diagonalRamsey_one : diagonalRamsey 1 = 1 := by
  rw [diagonalRamsey.def, ramseyNumber_one_succ]

@[simp]
theorem diagonalRamsey_two : diagonalRamsey 2 = 2 := by
  rw [diagonalRamsey.def, ramseyNumber_cons_two, ramseyNumber_singleton]

theorem diagonalRamsey_monotone : Monotone diagonalRamsey := fun _ _ hnm ↦
  ramseyNumber.mono_two hnm hnm

theorem ramseyNumber_le_choose : ∀ i j : ℕ, ramseyNumber ![i, j] ≤ (i + j - 2).choose (i - 1)
  | 0, _ => by simp
  | _, 0 => by rw [ramseyNumber_pair_swap, ramseyNumber_cons_zero]; exact zero_le
  | 1, j + 1 => by rw [ramseyNumber_one_succ, Nat.choose_zero_right]
  | i + 1, 1 => by rw [ramseyNumber_succ_one, Nat.succ_sub_succ_eq_sub, Nat.choose_self]
  | i + 2, j + 2 => by
    refine (ramseyNumber_two_colour_bound_aux (Nat.le_add_left _ _) (Nat.le_add_left _ _)).trans ?_
    rw [Nat.add_succ_sub_one, Nat.add_succ_sub_one, ← add_assoc, Nat.add_sub_cancel]
    refine (add_le_add (ramseyNumber_le_choose _ _) (ramseyNumber_le_choose _ _)).trans ?_
    rw [add_add_add_comm, Nat.add_sub_cancel, ← add_assoc, Nat.add_sub_cancel, add_add_add_comm,
      add_right_comm i 2, Nat.choose_succ_succ (i + j + 1) i]
    rfl

theorem diagonalRamsey_le_centralBinom (i : ℕ) : diagonalRamsey i ≤ (i - 1).centralBinom :=
  (ramseyNumber_le_choose i i).trans_eq
    (by rw [Nat.centralBinom_eq_two_mul_choose, Nat.mul_sub_left_distrib, mul_one, two_mul])

theorem diagonalRamsey_le_central_binom' (i : ℕ) : diagonalRamsey i ≤ i.centralBinom :=
  (diagonalRamsey_le_centralBinom _).trans (Nat.centralBinom_strictMono.monotone (Nat.sub_le _ _))

theorem ramseyNumber_pair_le_two_pow {i j : ℕ} : ramseyNumber ![i, j] ≤ 2 ^ (i + j - 2) :=
  (ramseyNumber_le_choose _ _).trans (Nat.choose_le_two_pow _ _)

theorem ramseyNumber_pair_le_two_pow' {i j : ℕ} : ramseyNumber ![i, j] ≤ 2 ^ (i + j) :=
  ramseyNumber_pair_le_two_pow.trans (pow_le_pow_right₀ one_le_two (Nat.sub_le _ _))

theorem diagonalRamsey_le_four_pow_sub_one {i : ℕ} : diagonalRamsey i ≤ 4 ^ (i - 1) :=
  ramseyNumber_pair_le_two_pow.trans_eq
    (by rw [show 4 = 2 ^ 2 from rfl, ← pow_mul, Nat.mul_sub_left_distrib, two_mul, mul_one])

theorem diagonalRamsey_le_four_pow {i : ℕ} : diagonalRamsey i ≤ 4 ^ i :=
  diagonalRamsey_le_four_pow_sub_one.trans (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))

/-- A good bound when i is small and j is large. For `i = 1, 2` this is equality (as long as
`j ≠ 0`), and for `i = 3` and `i = 4` it is the best possible polynomial upper bound, although
lower order improvements are available. -/
theorem ramseyNumber_le_right_pow_left (i j : ℕ) : ramseyNumber ![i, j] ≤ j ^ (i - 1) :=
  by
  rcases Nat.eq_zero_or_pos j with (rfl | hj)
  · rw [ramseyNumber_pair_swap, ramseyNumber_cons_zero]
    exact zero_le
  refine (ramseyNumber_le_choose i j).trans ?_
  have : i + j - 2 ≤ i - 1 + (j - 1) := add_tsub_add_le_tsub_add_tsub.trans' le_rfl
  -- the way naturals are handled in lean 4 makes me need to change this proof
  refine (Nat.choose_le_choose _ this).trans ?_
  rw [add_comm]
  refine (Nat.choose_add_le_add_one_pow _ _).trans_eq ?_
  rw [Nat.sub_add_cancel hj]

/-- A simplification of `ramsey_number_le_right_pow_left` which is more convenient for asymptotic
reasoning. A good bound when `i` is small and `j` is very large. -/
theorem ramseyNumber_le_right_pow_left' {i j : ℕ} : ramseyNumber ![i, j] ≤ j ^ i :=
  (ramseyNumber_le_right_pow_left (i + 1) j).trans' <| ramseyNumber.mono_two (by simp) le_rfl

end SimpleGraph
