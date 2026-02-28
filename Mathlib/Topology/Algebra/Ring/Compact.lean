/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.GroupTheory.Divisible
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Algebra.Ring.Ideal

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

/-- A connected compact Hausdorff vector space over `𝔽_p` is trivial.
This might sound easy, but it might require existence of continuous characters.
Here's a proof, using existence of continuous characters:
If `χ : A → circle` is a continuous character, then the image of `χ` is connected but is a
subgroup of the `p`th roots of unity, hence trivial. Thus, `A` has no nontrivial continuous
characters, and this implies that `A` is trivial. -/
@[to_additive]
theorem Group.tricky
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [ConnectedSpace A] [CompactSpace A] [T2Space A]
    (p : ℕ) (hp : p.Prime) (hAp : ∀ a : A, a ^ p = 1) :
    Subsingleton A := by
  sorry

/-- A compact Hausdorff vector space over `𝔽_p` is totally disconnected. -/
@[to_additive]
theorem Group.tricky'
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [CompactSpace A] (p : ℕ) (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) :
    TotallyDisconnectedSpace A := by
  have : ConnectedSpace (Subgroup.connectedComponentOfOne A) :=
    Subtype.connectedSpace isConnected_connectedComponent
  have : CompactSpace (Subgroup.connectedComponentOfOne A) :=
    isCompact_iff_compactSpace.mp (isClosed_connectedComponent.isCompact)
  have := Group.tricky (Subgroup.connectedComponentOfOne A) p hp (fun a ↦ Subtype.ext (hA a))
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  exact ((Set.subsingleton_coe _).mp this).eq_singleton_of_mem mem_connectedComponent

/-- A connected compact Hausdorff abelian topological group is divisible. -/
@[to_additive]
noncomputable def Group.rootable
    (A : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [ConnectedSpace A] [CompactSpace A] [T2Space A] : RootableBy A ℕ := by
  apply rootableByOfPowLeftSurj
  suffices ∀ p : ℕ, p.Prime → Function.Surjective fun a : A ↦ a ^ p by
    apply Nat.prime_composite_induction
    · simp
    · simpa using Function.surjective_id
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
  have := tricky' (A ⧸ f.range) p hp hf
  have : ConnectedSpace (A ⧸ f.range) :=
    QuotientGroup.mk_surjective.connectedSpace QuotientGroup.continuous_mk
  rw [← MonoidHom.range_eq_top, ← QuotientGroup.subsingleton_iff]
  exact subsingleton_of_preconnected_totallyDisconnected

/-- A connected compact Hausdorff abelian topological group does not admit a nontrivial compact
group of automorphisms. -/
@[to_additive]
theorem CommGroup.no_compact_automorphisms
    {A : Type*} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [ConnectedSpace A] [CompactSpace A] [T2Space A] (K : Subgroup (ContinuousMonoidHom A A))
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

/-- A compact Hausdorff ring is totally disconnected. -/
instance {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] : TotallyDisconnectedSpace R := by
  let C₀ : Ideal R := Ideal.connectedComponentOfZero R
  suffices C₀ = ⊥ from
    totallyDisconnectedSpace_iff_connectedComponent_zero.mpr (SetLike.ext'_iff.mp this)
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
  have key := AddCommGroup.no_compact_automorphisms f.range (isCompact_range f.continuous)
  refine eq_bot_iff.mpr fun c hc ↦ ?_
  replace key : f.toAddMonoidHom 1 ⟨c, hc⟩ = (0 : ContinuousAddMonoidHom C₀ C₀) ⟨c, hc⟩ := by
    rw [AddMonoidHom.range_eq_bot_iff.mp key, AddMonoidHom.zero_apply]
  exact (one_smul R c).symm.trans (Subtype.ext_iff.mp key)

end CompactHausdorff
