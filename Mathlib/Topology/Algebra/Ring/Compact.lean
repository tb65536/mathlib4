/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.GroupTheory.Divisible
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!

# Compact Hausdorff Rings

## Main results
- `IsArtinianRing.finite_of_compactSpace_of_t2Space`:
  Compact Hausdorff Artinian rings are finite (and thus discrete).
- `Ideal.isOpen_of_isMaximal`:
  Maximal ideals are open in compact Hausdorff Noetherian rings.
- `IsLocalRing.isOpen_iff_finite_quotient`:
  An ideal in a compact Hausdorff Noetherian local ring is open iff it has finite index.
- `IsDedekindDomain.isOpen_iff`:
  An ideal in a compact Hausdorff Dedekind domain (that is not a field) is open iff it is non-zero.

## Future projects
Show that compact Hausdorff rings are totally disconnected and linearly topologized.
See https://ncatlab.org/nlab/show/compact+Hausdorff+rings+are+profinite

-/

@[expose] public section

attribute [local instance] Ideal.Quotient.field Fintype.ofFinite finite_of_compact_of_discrete
  DivisionRing.finite_of_compactSpace_of_t2Space

variable {R : Type*} [CommRing R] [TopologicalSpace R]
variable [IsTopologicalRing R] [CompactSpace R] [T2Space R]

namespace IsArtinianRing

/-- Compact Hausdorff Artinian (commutative) rings are finite. This is not an instance, as it would
apply to every `Finite` goal, causing slowly failing typeclass search in some cases. -/
theorem finite_of_compactSpace_of_t2Space [IsArtinianRing R] :
    Finite R := by
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have H : (∏ p : PrimeSpectrum R, p.asIdeal) ^ n = ⊥ := by
    rw [← le_bot_iff, ← Ideal.zero_eq_bot, ← hn]
    gcongr
    rw [Ideal.jacobson_bot, Ring.jacobson_eq_sInf_isMaximal, le_sInf_iff]
    exact fun I hI ↦ Ideal.prod_le_inf.trans
      (Finset.inf_le (b := PrimeSpectrum.mk I hI.isPrime) (by simp))
  have := Ideal.finite_quotient_prod (R := R) PrimeSpectrum.asIdeal Finset.univ
    (fun _ _ ↦ IsNoetherian.noetherian _) (fun _ _ ↦ inferInstance)
  have := Ideal.finite_quotient_pow (IsNoetherian.noetherian (∏ p : PrimeSpectrum R, p.asIdeal)) n
  rw [H] at this
  exact .of_equiv _ (RingEquiv.quotientBot R).toEquiv

end IsArtinianRing

section IsNoetherianRing

variable [IsNoetherianRing R]

lemma Ideal.isOpen_of_isMaximal (I : Ideal R) [I.IsMaximal] : IsOpen (X := R) I :=
  have : I.toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (inferInstanceAs (Finite (R ⧸ I)))
  I.toAddSubgroup.isOpen_of_isClosed_of_finiteIndex (inferInstanceAs (IsClosed (X := R) I))

lemma Ideal.isOpen_pow_of_isMaximal (I : Ideal R) [I.IsMaximal] (n : ℕ) :
    IsOpen (X := R) ↑(I ^ n) :=
  have : (I ^ n).toAddSubgroup.FiniteIndex :=
    @AddSubgroup.finiteIndex_of_finite_quotient _ _ _
      (Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _)
  (I ^ n).toAddSubgroup.isOpen_of_isClosed_of_finiteIndex
    (Ideal.isCompact_of_fg (IsNoetherian.noetherian _)).isClosed

-- Note: this is only by infer_instance because of the opened local instances.
instance (priority := low) (I : Ideal R) [I.IsMaximal] : Finite (R ⧸ I) := inferInstance

end IsNoetherianRing

namespace IsLocalRing

variable [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
lemma isOpen_maximalIdeal_pow (n : ℕ) :
    IsOpen (X := R) ↑(maximalIdeal R ^ n) :=
  Ideal.isOpen_pow_of_isMaximal _ _

variable (R) in
lemma isOpen_maximalIdeal : IsOpen (X := R) ↑(maximalIdeal R) :=
  Ideal.isOpen_of_isMaximal _

instance finite_residueField_of_compactSpace : Finite (ResidueField R) :=
  inferInstanceAs (Finite (R ⧸ _))

lemma isOpen_iff_finite_quotient {I : Ideal R} :
    IsOpen (X := R) I ↔ Finite (R ⧸ I) := by
  refine ⟨AddSubgroup.quotient_finite_of_isOpen I.toAddSubgroup, fun H ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  exact AddSubgroup.isOpen_mono (H₁ := (maximalIdeal R ^ n).toAddSubgroup)
    (H₂ := I.toAddSubgroup) hn (isOpen_maximalIdeal_pow R n)

end IsLocalRing

section IsDedekindDomain

lemma IsDedekindDomain.isOpen_of_ne_bot
    [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) :
    IsOpen (X := R) I := by
  rw [← Ideal.finprod_heightOneSpectrum_factorization hI,
    finprod_eq_finset_prod_of_mulSupport_subset _
      (s := (Ideal.finite_mulSupport hI).toFinset) (by simp)]
  refine @AddSubgroup.isOpen_of_isClosed_of_finiteIndex _ _ _ _ (Submodule.toAddSubgroup _)
    ?_ (IsNoetherianRing.isClosed_ideal _)
  refine @AddSubgroup.finiteIndex_of_finite_quotient _ _ _ ?_
  refine Ideal.finite_quotient_prod _ _ (fun _ _ ↦ IsNoetherian.noetherian _) fun _ _ ↦ ?_
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _

lemma IsDedekindDomain.isOpen_iff
    [IsDedekindDomain R] (hR : ¬ IsField R) {I : Ideal R} :
    IsOpen (X := R) I ↔ I ≠ ⊥ := by
  refine ⟨?_, IsDedekindDomain.isOpen_of_ne_bot⟩
  rintro H rfl
  have := discreteTopology_iff_isOpen_singleton_zero.mpr H
  exact hR (Finite.isField_of_domain R)

lemma IsDiscreteValuationRing.isOpen_iff
    [IsDomain R] [IsDiscreteValuationRing R] {I : Ideal R} :
    IsOpen (X := R) I ↔ I ≠ ⊥ :=
  IsDedekindDomain.isOpen_iff (not_isField R)

end IsDedekindDomain

section CompactHausdorff

-- PRed
@[to_additive] -- todo: to_additivize `instIsMulTorsionFree` in `Algebra/Group/Subgroup/Basic`.
instance instIsMulTorsionFree
    {G : Type*} [Group G] (H : Subgroup G) [IsMulTorsionFree G] : IsMulTorsionFree H where
  pow_left_injective n hn a b := by
    have := pow_left_injective hn (M := G) (a₁ := a) (a₂ := b)
    dsimp at *
    norm_cast at this

open Pointwise in
def Ideal.connectedComponentOfZero
    (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R] : Ideal R where
  __ := AddSubgroup.connectedComponentOfZero R
  smul_mem' := by
    intro c x h
    let f : R → R := fun y ↦ c * y
    have key : Continuous f := continuous_mul_left c
    suffices f '' connectedComponent (0 : R) ⊆ connectedComponent (0 : R) from this ⟨x, h, rfl⟩
    apply IsConnected.subset_connectedComponent
    · exact isConnected_connectedComponent.image _ key.continuousOn
    · exact ⟨0, mem_connectedComponent, mul_zero c⟩

theorem foobar {α : Type*} [TopologicalSpace α] [ConnectedSpace α] [TotallyDisconnectedSpace α] :
    Subsingleton α := by
  refine ⟨fun a b ↦ ?_⟩
  rw [← Set.singleton_eq_singleton_iff,
    ← connectedComponent_eq_singleton, ← connectedComponent_eq_singleton,
    PreconnectedSpace.connectedComponent_eq_univ, PreconnectedSpace.connectedComponent_eq_univ]

universe u

def MyGroup (n : ℕ) : Type := Multiplicative (ZMod n)

instance MyGroupGroup (n : ℕ) : Group (MyGroup n) := sorry

instance MyGroupTopologicalSpace (n : ℕ) : TopologicalSpace (MyGroup n) := sorry

def MyAddGroup (n : ℕ) : Type := ZMod n

instance MyAddGroupAddGroup (n : ℕ) : AddGroup (MyAddGroup n) := sorry

instance MyAddGroupTopologicalSpace (n : ℕ) : TopologicalSpace (MyAddGroup n) := sorry

attribute [to_additive existing] MyGroup MyGroupGroup MyGroupTopologicalSpace

@[to_additive]
theorem card_myGroup (n : ℕ) : Nat.card (MyGroup n) = n := by
  exact Nat.card_zmod n


@[to_additive]
theorem Group.foo' (A : Type u) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] (p : ℕ) (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hA : ConnectedSpace A) :
    Subsingleton A := by
  contrapose! hA
  let α := Σ B : Subgroup A, {f : B →* MyGroup p | Function.Surjective f ∧ Continuous f}
  have : Nonempty α := sorry
  let r : α → α → Prop :=
    fun f g ↦ f.1 ≤ g.1 ∧ ∀ (x : f.1) (y : g.1), x.1 = y.1 → f.2.1 x = g.2.1 y
  have trans : ∀ {f g h}, r f g → r g h → r f h := by
    intro f g h rfg rgh
    refine ⟨rfg.1.trans rgh.1, fun x z hxz ↦ ?_⟩
    let y : g.1 := ⟨x.1, rfg.1 x.2⟩
    exact (rfg.2 x y rfl).trans (rgh.2 y z hxz)
  have chain : ∀ s, IsChain r s → s.Nonempty → ∃ f, ∀ g ∈ s, r g f := by
    intro s hsc hs
    refine ⟨⟨⨆ f ∈ s, f.1, ?_, ?_, ?_⟩, ?_⟩
    all_goals sorry
  obtain ⟨f, hf⟩ := exists_maximal_of_nonempty_chains_bounded chain trans
  suffices f.1 = ⊤ by
    rw [connectedSpace_iff_clopen]

    -- disconnect
    sorry
  contrapose! hf
  obtain ⟨a, ha⟩ := SetLike.exists_not_mem_of_ne_top f.1 hf
  let B := f.1 ⊔ Subgroup.zpowers a
  let C := f.2.1.ker.map f.1.subtype -- index p in f.1
  have h1 : C.relIndex f.1 = p := by
    rw [← f.1.range_subtype, f.1.subtype.range_eq_map,
      Subgroup.relIndex_map_map_of_injective _ _ f.1.subtype_injective, Subgroup.relIndex_top_right,
      Subgroup.index_ker, f.2.1.range_eq_top_of_surjective f.2.2.1, Subgroup.card_top]
    exact card_myGroup p
  have h2 : f.1.relIndex B = p := by
    rw [Subgroup.relIndex_sup_left]
    sorry
  have h3 : C ≤ f.1 := Subgroup.map_subtype_le f.2.1.ker
  have h4 : f.1 ≤ B := le_sup_left
  refine ⟨⟨B, ?_, ?_, ?_⟩, ?_⟩
  sorry
  -- idea: if not the whole space yet, then we have a subspace of index p^2
  -- what is it's closure?
  -- if index p, then we're good (quotient)
  -- if index p^2, then still good (take translates)

@[to_additive]
theorem Group.foo (A : Type u) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] (p : ℕ) (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) :
    TotallyDisconnectedSpace A := by
  -- quotient by connected component of the identity, giving totally disconnected
  sorry

@[to_additive]
noncomputable def Group.rootable
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [ConnectedSpace A] [T2Space A] : RootableBy A ℕ := by
  apply rootableByOfPowLeftSurj
  suffices ∀ p : ℕ, p.Prime → Function.Surjective fun a : A ↦ a ^ p by
    apply Nat.prime_composite_induction
    · simp
    · simp [← Function.id_def, Function.surjective_id]
    · grind
    · intro a _ ha b _ hb _
      simp only [pow_mul]
      exact (hb (by grind)).comp (ha (by grind))
  intro p hp
  let f : A →* A := powMonoidHom p
  change Function.Surjective f
  have hf : ∀ a : A ⧸ f.range, a ^ p = 1 := by
    intro a
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨a, rfl⟩
  have : IsClosed (f.range : Set A) := (isCompact_range (continuous_pow p)).isClosed
  have := foo (A ⧸ f.range) p hp hf
  have : ConnectedSpace (A ⧸ f.range) :=
    QuotientGroup.mk_surjective.connectedSpace QuotientGroup.continuous_mk
  rw [← MonoidHom.range_eq_top, ← QuotientGroup.subsingleton_iff]
  exact foobar

-- PRed
@[to_additive]
theorem ContinuousMonoidHom.mul_apply {A B : Type*} [Monoid A] [CommMonoid B]
    [TopologicalSpace A] [TopologicalSpace B] [ContinuousMul B]
    (f g : ContinuousMonoidHom A B) (a : A) : (f * g) a = f a * g a := by
  rfl

-- PRed
@[to_additive]
theorem ContinuousMonoidHom.pow_apply {A B : Type*} [Monoid A] [CommMonoid B]
    [TopologicalSpace A] [TopologicalSpace B] [ContinuousMul B]
    (f : ContinuousMonoidHom A B) (n : ℕ) (a : A) : (f ^ n) a = (f a) ^ n := by
  induction n
  case zero => simp
  case succ n ih =>
    rw [pow_succ, pow_succ, ContinuousMonoidHom.mul_apply, ih]

open Pointwise in
@[to_additive]
theorem CommGroup.foo {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [ConnectedSpace A] [T2Space A] (K : Subgroup (ContinuousMonoidHom A A))
    (hK : IsCompact (K : Set (ContinuousMonoidHom A A))) :
    K = ⊥ := by
  have A_rootable : RootableBy A ℕ := Group.rootable A
  rw [eq_bot_iff]
  intro f hf
  ext a
  rw [ContinuousMonoidHom.one_toFun]
  by_contra! ha
  let U : Set A := {f a}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  have hU1 : 1 ∈ U := ha.symm
  let W : Set (A →ₜ* A) := {f | Set.MapsTo f Set.univ U}
  have hW : IsOpen W :=
    (ContinuousMonoidHom.isInducing_toContinuousMap A A).continuous.isOpen_preimage _
      (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ hU)
  have hW1 : 1 ∈ W := by simpa [W]
  replace hW1 : W ∈ nhds 1 := hW.mem_nhds hW1
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨n, hn0, hnf⟩ :=
    (mapClusterPt_iff_frequently.mp (mapClusterPt_one_atTop_pow ⟨f, hf⟩) (Subtype.val ⁻¹' W)
    (continuousAt_subtype_val.preimage_mem_nhds (by exact hW1))).forall_exists_of_atTop 1
  replace hn0 : n ≠ 0 := by grind
  rw [Set.mem_preimage, Subgroup.coe_pow, Subtype.coe_mk,
    Set.mem_setOf_eq, Set.mapsTo_univ_iff, ← Set.range_subset_iff] at hnf
  change (f ^ n).range ≤ U at hnf
  suffices f.range ≤ (f ^ n).range by
    exact (Set.Subset.trans this hnf) ⟨a, rfl⟩ rfl
  rintro - ⟨b, rfl⟩
  use RootableBy.root b n
  simp [ContinuousMonoidHom.pow_apply, ← map_pow, RootableBy.root_cancel b hn0]

instance {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] : TotallyDisconnectedSpace R := by
  let C₀ : Ideal R := Ideal.connectedComponentOfZero R
  suffices C₀ = ⊥ by
    replace this : connectedComponent (0 : R) = {0} := SetLike.ext'_iff.mp this
    rw [totallyDisconnectedSpace_iff_connectedComponent_subsingleton]
    intro x
    have key := (continuous_add_left (-x)).image_connectedComponent_subset x
    rw [neg_add_cancel, this, Set.image_subset_iff] at key
    -- this can probably be done more cleanly...
    exact Set.subsingleton_of_forall_eq x (by simpa using key)
  have C₀_isClosed : IsClosed (C₀ : Set R) := isClosed_connectedComponent
  have C₀_isCompact : IsCompact (C₀ : Set R) := C₀_isClosed.isCompact
  have : CompactSpace C₀ := isCompact_iff_compactSpace.mp C₀_isCompact
  have C₀_isConnected : IsConnected (C₀ : Set R) := isConnected_connectedComponent
  have : ConnectedSpace C₀ := isConnected_iff_connectedSpace.mp C₀_isConnected
  let f : ContinuousAddMonoidHom R (ContinuousAddMonoidHom C₀ C₀) :=
  { toFun r :=
    { toFun := fun c ↦ r • c
      map_zero' := by simp
      map_add' := by simp [smul_add]
      continuous_toFun := by fun_prop }
    map_zero' := by apply DFunLike.ext; intros; apply zero_smul
    map_add' := by intros; apply DFunLike.ext; intros; apply add_smul
    continuous_toFun := ContinuousAddMonoidHom.continuous_of_continuous_uncurry _ continuous_smul }
  have key := AddCommGroup.foo f.range (isCompact_range f.continuous)
  refine eq_bot_iff.mpr fun c hc ↦ ?_
  replace key : f.toAddMonoidHom 1 ⟨c, hc⟩ = (0 : ContinuousAddMonoidHom C₀ C₀) ⟨c, hc⟩ := by
    rw [AddMonoidHom.range_eq_bot_iff.mp key, AddMonoidHom.zero_apply]
  replace key : (1 : R) • c = 0 := Subtype.ext_iff.mp key
  rwa [one_smul] at key

end CompactHausdorff
