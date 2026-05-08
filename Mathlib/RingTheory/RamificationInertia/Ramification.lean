/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Ramification index

Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

## Main definitions

* `Ideal.ramificationIdx' q R`: The ramification index of `q` over `R`.

## Main statements

* `ramificationIdx_eq_ramificationIdx'`: The ramification index agrees with the usual definition in
  the case of Dedekind domains.
* `ramificationIdx'_tower`: Ramification index is multiplicative in towers.

-/

@[expose] public section

namespace Ideal

section

variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]

open Classical in
/-- Let `S/R` be an extension of rings, and let `q` be a prime ideal of `S` lying over a prime ideal
`p` of `R`. Let `Sq` be the localization of `S` and `q`, and let `pSq` be the image of `p` in `Sq`.
Then the ramification index of `q` over `R` is defined to be the length of the quotient `Sq/pSq` as
an `Sq`-module.

When `q` is not prime, we use a junk value of `0`.

This will eventually replace the existing definition of `Ideal.ramificationIdx`. -/
noncomputable def ramificationIdx' : ℕ :=
  if _ : q.IsPrime then
    letI Sq := Localization.AtPrime q
    (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat
  else 0

theorem ramificationIdx'_def [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ (q.under R).map (algebraMap R Sq))).toNat :=
  dif_pos _

theorem ramificationIdx'_of_not_isPrime (hq : ¬ q.IsPrime) : q.ramificationIdx' R = 0 :=
  dif_neg hq

-- PRed
theorem IsIntegral.comap_lt_comap (R : Type*) {A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.IsIntegral R A] {I J : Ideal A} [I.IsPrime] (I_lt_J : I < J) :
    I.comap (algebraMap R A) < J.comap (algebraMap R A) :=
  let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
  comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (Algebra.IsIntegral.isIntegral x)

theorem ramificationIdx'_pos [hq : q.IsPrime] [IsNoetherianRing S]
    [Algebra.IsIntegral R S] : 0 < q.ramificationIdx' R := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  rw [ramificationIdx'_def, Nat.pos_iff_ne_zero, ne_eq, ENat.toNat_eq_zero, not_or]
  constructor
  · rw [Module.length_eq_zero_iff, Submodule.Quotient.subsingleton_iff,
      IsScalarTower.algebraMap_eq R S, ← map_map, ← ne_eq, ← lt_top_iff_ne_top]
    refine lt_of_le_of_lt (map_mono map_comap_le) ?_
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    refine IsMaximal.lt_top ?_
    exact IsLocalRing.maximalIdeal.isMaximal (Localization q.primeCompl)
  · rw [← ne_eq, Module.length_eq_of_surjective
        (R := Sq ⧸ p.map (algebraMap R Sq)) (S := Sq) Quotient.mk_surjective,
      Module.length_ne_top_iff, ← isArtinianRing_iff_isFiniteLength,
      isArtinianRing_iff_krullDimLE_zero]
    have : q ∈ (p.map (algebraMap R S)).minimalPrimes := by
      refine ⟨⟨hq, map_comap_le⟩, ?_⟩
      intro r ⟨hr, hpr⟩ hrq
      rw [map_le_iff_le_comap] at hpr
      contrapose! hpr
      exact not_le_of_gt (IsIntegral.comap_lt_comap R (lt_of_le_not_ge hrq hpr))
    have : q.map (algebraMap S Sq) ∈ (p.map (algebraMap R Sq)).minimalPrimes := by
      rwa [IsScalarTower.algebraMap_eq R S Sq, ← map_map,
        IsLocalization.minimalPrimes_map q.primeCompl, Set.mem_preimage,
        Localization.AtPrime.map_eq_maximalIdeal,
        IsLocalization.AtPrime.comap_maximalIdeal Sq q]
    rw [Ring.krullDimLE_zero_iff]
    intro r hr
    let r' := r.comap (algebraMap Sq (Sq ⧸ p.map (algebraMap R Sq)))
    suffices r'.IsMaximal by
      exact r.isMaximal_of_isIntegral_of_isMaximal_comap this
    replace hr : r'.IsPrime := hr.comap _
    have key : p.map (algebraMap R Sq) ≤ r' := by
      rw [← (p.map (algebraMap R Sq)).mk_ker]
      apply Ideal.ker_le_comap
    rw [Localization.AtPrime.map_eq_maximalIdeal] at this
    have := this.2 ⟨hr, key⟩ (IsLocalRing.le_maximalIdeal_of_isPrime r')
    rw [← Ideal.IsMaximal.eq_of_le ?_ hr.ne_top this]
    · exact IsLocalRing.maximalIdeal.isMaximal Sq
    · exact IsLocalRing.maximalIdeal.isMaximal Sq

theorem ramificationIdx'_eq_one [q.IsPrime] [Algebra.IsUnramifiedAt R q]
    [Algebra.EssFiniteType R S] : q.ramificationIdx' R = 1 := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  rw [ramificationIdx'_def, ENat.toNat_eq_iff_eq_coe, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff,
    IsScalarTower.algebraMap_eq R Rp Sq, ← map_map, Localization.AtPrime.map_eq_maximalIdeal]
  exact Algebra.FormallyUnramified.map_maximalIdeal

theorem ramificationIdx'_eq_one_iff [q.IsPrime] [Algebra.EssFiniteType R S]
    [Algebra.IsIntegral R S] [PerfectField (q.under R).ResidueField] :
    q.ramificationIdx' R = 1 ↔ Algebra.IsUnramifiedAt R q := by
  let p := q.under R
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.EssFiniteType Rp Sq := Algebra.EssFiniteType.of_comp R Rp Sq
  have : Algebra.IsSeparable p.ResidueField q.ResidueField :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  rw [ramificationIdx'_def, ENat.toNat_eq_iff_eq_coe, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff,
    IsScalarTower.algebraMap_eq R Rp Sq, ← map_map, Localization.AtPrime.map_eq_maximalIdeal]
  transitivity Algebra.FormallyUnramified Rp Sq
  · rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq, and_iff_right]
    assumption
  · -- add iff version
    exact ⟨fun _ ↦ Algebra.FormallyUnramified.comp R Rp Sq, fun _ ↦ inferInstance⟩

end

section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  (p : Ideal R) (q : Ideal S) (r : Ideal T)

theorem ramificationIdx'_eq [q.LiesOver p] [q.IsPrime] :
    letI Sq := Localization.AtPrime q
    q.ramificationIdx' R = (Module.length Sq (Sq ⧸ p.map (algebraMap R Sq))).toNat := by
  rw [ramificationIdx'_def, over_def q p]

open Pointwise in
theorem ramificationIdx'_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    (g : G) : (g • q).ramificationIdx' R = q.ramificationIdx' R := by
  by_cases hq : q.IsPrime; swap
  · rw [ramificationIdx'_of_not_isPrime, ramificationIdx'_of_not_isPrime] <;> simpa
  · let p := q.under R
    let := Localization.AtPrime.algebraOfLiesOver p q
    let := Localization.AtPrime.algebraOfLiesOver p (g • q)
    rw [ramificationIdx'_eq p q, ramificationIdx'_eq p (g • q)]
    congr 1
    sorry

open Localization IsLocalization.AtPrime in
theorem ramificationIdx_eq_ramificationIdx'
    [IsDomain R] [IsDedekindDomain S] [Module.IsTorsionFree R S]
    [q.LiesOver p] [hq : q.IsPrime] (hp : p ≠ ⊥) :
    p.ramificationIdx q = q.ramificationIdx' R := by
  have : p.IsPrime := isPrime_of_liesOver q p
  have hq' : q ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot hp q
  have : q.IsMaximal := hq.isMaximal hq'
  have hpS : p.map (algebraMap R S) ≠ ⊥ := map_ne_bot_of_ne_bot hp
  obtain ⟨I, hqI, h⟩ := Ideal.eq_prime_pow_mul_coprime hpS q
  replace hqI : ¬ I ≤ q := by
    contrapose! hqI
    rw [sup_of_le_left hqI]
    exact hq.ne_top
  rw [← IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hpS hq hq'] at h
  apply_fun (map (algebraMap S (Localization.AtPrime q))) at h
  rw [map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_mul, Ideal.map_pow,
    map_eq_top_of_not_le (Localization.AtPrime q) hqI, mul_top, AtPrime.map_eq_maximalIdeal] at h
  have hSq := isDiscreteValuationRing_of_dedekind_domain S hq' (Localization.AtPrime q)
  rw [ramificationIdx'_eq p q, h, hSq.length_quotient_pow_maximalIdeal, ENat.toNat_coe]

/-- See `ramificationIdx'_tower` for a version that does not assume primality. -/
theorem ramificationIdx'_tower' [q.IsPrime] [r.IsPrime] [r.LiesOver q]
    [Algebra (Localization.AtPrime q) (Localization.AtPrime r)]
    [Localization.AtPrime.IsLiesOverAlgebra q r]
    [Module.Flat (Localization.AtPrime q) (Localization.AtPrime r)] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  have : q.LiesOver (r.under R) := LiesOver.tower_bot r q (r.under R)
  let f := (Ideal.quotientEquivAlgOfEq (Localization.AtPrime r)
    (by rw [map_map, ← IsScalarTower.algebraMap_eq])).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (Localization.AtPrime r)
        ((r.under R).map (algebraMap R (Localization.AtPrime q))))
  rw [ramificationIdx'_def, ramificationIdx'_eq (r.under R), ramificationIdx'_eq q,
    f.toLinearEquiv.length_eq, IsLocalRing.length_baseChange, ENat.toNat_mul,
    ← Localization.AtPrime.map_eq_maximalIdeal, map_map, ← IsScalarTower.algebraMap_eq]

/-- See `ramificationIdx'_tower'` for a version that only assumes local flatness. -/
theorem ramificationIdx'_tower [r.LiesOver q] [Module.Flat S T] :
    r.ramificationIdx' R = q.ramificationIdx' R * r.ramificationIdx' S := by
  by_cases hr : r.IsPrime
  · have : q.IsPrime := isPrime_of_liesOver r q
    let := Localization.AtPrime.algebraOfLiesOver q r
    apply ramificationIdx'_tower'
  · rw [ramificationIdx'_of_not_isPrime r R hr, ramificationIdx'_of_not_isPrime r S hr, mul_zero]

end

end Ideal
