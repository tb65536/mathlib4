module

public import Mathlib.NumberTheory.RamificationInertia.Galois

open scoped IntermediateField

section PrimitiveElementTheorem

/-
**The primitive element theorem**

If `E/F` is a finite separable field extension,
then `E = F(α)` for some `α ∈ E`.
-/

-- The primitive element theorem in Mathlib
#check Field.exists_primitive_element

-- Let `E/F` be a field extension
variable (F E : Type*) [Field F] [Field E] [Algebra F E]

-- Assume that `E/F` is finite and separable
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

-- The primitive element theorem for `E/F`
#check Field.exists_primitive_element F E

-- Without the fancy notation for adjoin
example : ∃ α : E, IntermediateField.adjoin F {α} = ⊤ := by
  exact Field.exists_primitive_element F E

-- Why can't we just write `F(α) = E`?
variable (α : E)
#check IntermediateField.adjoin
#check F⟮α⟯
#check E
#check (⊤ : IntermediateField F E)

end PrimitiveElementTheorem

section GaloisExtensions

/-
**Galois extensions**

For a finite field extension `E/F`, the following are equivalent:
* `E/F` is normal and separable (the definition of Galois)
* `E^G = F` (`F` is the subfield of `E` fixed pointwise by `G`)
* `|Gal(E/F)| = [E : F]` (`E/F` has degree-many automorphisms)
* `E` is the splitting field of a separable polynomial over `F`
-/

-- The characterization of Galois extensions in mathlib
#check IsGalois.tfae

-- Let `E/F` be a finite field extension
variable (F E : Type*) [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E]

-- The characterization of Galois extensions for `E/F`
#check IsGalois.tfae (F := F) (E := E)

-- `E/F` is normal and separable (the definition of Galois)
#check IsGalois F E

-- `E^G = F` (`F` is the subfield of `E` fixed pointwise by `G`)
#check IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) =
  (⊥ : IntermediateField F E)

-- `Gal(E/F)` is notation for `F`-algebra automorphisms of `E`
example : Gal(E/F) = (E ≃ₐ[F] E) := rfl

-- Why can't we just write `E^G = F`?
#check IntermediateField.fixedField (F := F) (E := E)
#check IntermediateField.fixingSubgroup (F := F) (E := E)

-- `|Gal(E/F)| = [E : F]` (`E/F` has degree-many automorphisms)
#check Nat.card Gal(E/F) = Module.finrank F E

-- `E` is the splitting field of a separable polynomial over `F`
#check ∃ p, p.Separable ∧ Polynomial.IsSplittingField F E p

end GaloisExtensions

section GaloisCorrespondence

/-
**Galois correspondence**

For a finite Galois extension `E/F`,
there is an order-reversing bijection

  intermediate fields `E/K/F` <---> subgroups `H ≤ Gal(E/F)`

defined by the maps
* `K ↦ Gal(E/K)` (the automorphisms of `E` fixing `K` pointwise)
* `H ↦ E^H` (the subfield of `E` fixed pointwise by `H`)
-/

-- The Galois correspondence in mathlib
#check IsGalois.intermediateFieldEquivSubgroup

-- Let `E/F` be a finite Galois extension
variable (F E : Type*) [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [IsGalois F E]

-- The maps between intermediate fields and subgroups
#check IntermediateField.fixedField (F := F) (E := E)
#check IntermediateField.fixingSubgroup (F := F) (E := E)

-- The Galois correspondence for `E/F`
#check IsGalois.intermediateFieldEquivSubgroup (F := F) (E := E)

-- Type of order-preserving bijections
#check OrderIso (IntermediateField F E) (Subgroup Gal(E/F))ᵒᵈ

-- Type synonym for order dual
#check OrderDual (Subgroup Gal(E/F))

end GaloisCorrespondence

section FrobeniusElements

/-
**Frobenius elements**

In the standard presentation of algebraic number theory,
you work with an `AKLB`-setup:

      Fields: `K → L          ℚ  →  ℚ(i)`
              `↑   ↑          ↑      ↑  `
       Rings: `A → B          ℤ  →  ℤ[i]`
              `∪   ∪          ∪      ∪  `
Prime ideals: `p ⊂ q         (2) ⊂ (1+i)`

If `L/K` is Galois, then `Gal(L/K)` acts on the set `S_p`
of prime ideals above `p`. The stabilizer subgroup`D_q`
of `q` is called the decomposition subgroup of `q`.

Two key facts:
* The action of `Gal(L/K)` on `S_p` is transitive
* The homomorphism `D_q → Gal((B/q)/(A/p))` is surjective.

Bourbaki realized that these results hold much more generally!

Let `G` be a finite group acting on a commutative ring `B`
with invariant subring `A`.
Let `S_p` denote the set of prime ideals above `p`.
Let `D_q` denote the stabilizer subgroup of `q`.

Two key facts:
* The action of `G` on `S_p` is transitive
* The homomorphism `D_q → Aut((B/q)/(A/p))` is surjective
-/

-- Let `B/A` be an extension of commutative rings
variable (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B]

-- Let `G` be a finite group acting on `B`
variable [Group G] [Finite G] [MulSemiringAction G B]

-- Assume that `G` fixes every element of `A`
variable [SMulCommClass G A B]

-- Assume that every element of `B` fixed by `G` lies in `A`
variable [Algebra.IsInvariant A B G]

-- Let `p` and `q` be prime ideals of `A` and `B`
variable (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime]

-- Assume that `q` lies over `p`
variable [q.LiesOver p]

-- The action of `G` on `S_p` is transitive
#check Algebra.IsInvariant.orbit_eq_primesOver A B G p q

-- The homomorphism `D_q → Aut((B/q)/(A/p))` is surjective.
#check Ideal.Quotient.stabilizerHom_surjective G p q

-- The homomorphism `D_q → Aut((B/q)/(A/p))`
#check Ideal.Quotient.stabilizerHom q p G

end FrobeniusElements

section IsGaloisGroup

/-
**Predicate for Galois groups of fields**

After defining `Algebra.IsInvariant`, we realized that it
provides a convenient characterization of Galois groups.
-/

-- Let `E/F` be a field extension
variable (F E : Type*) [Field F] [Field E] [Algebra F E]

-- Let `G` be a group acting on `E`
variable (G : Type*) [Group G] [MulSemiringAction G E]

-- Assume that `G` is the Galois group of `E/F`
variable [IsGaloisGroup G F E]

-- Then `E/F` has degree-many automorphisms
#check IsGaloisGroup.card_eq_finrank G F E

end IsGaloisGroup

section IsGaloisGroup

/-
**Predicate for Galois groups of ring**

After defining `IsGaloisGroup`, we realized that the definition
doesn't require fields, and is actually useful for rings as well.
-/

-- Let `B/A` be an extension of commutative rings
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

-- Let `G` be a group acting on `B`
variable (G : Type*) [Group G] [MulSemiringAction G B]

-- Assume that `G` is the Galois group of `B/A`
variable [IsGaloisGroup G A B]

-- Assume that `A → B` is injective, `B` is a domain, and `G` is finite
variable [FaithfulSMul A B] [IsDomain B] [Finite G]

-- Then `B/A` has degree-many automorphisms
#check IsGaloisGroup.card_eq_finrank' G A B

end IsGaloisGroup

section RamificationTheory

/-
**Ramification theory**

In the standard presentation of algebraic number theory,
you work with an `AKLB`-setup:

      Fields: `K → L          ℚ  →  ℚ(i)`
              `↑   ↑          ↑      ↑  `
       Rings: `A → B          ℤ  →  ℤ[i]`
              `∪   ∪          ∪      ∪  `
Prime ideals: `p ⊂ q         (2) ⊂ (1+i)`

Then `∑_q e_q * f_q = [L : K]` where:
* `e_q` is the ramification index of `q` over `p`
* `f_q` is the ramification index of `q` over `p`

Again, this generalizes massively!
-/

-- Let `B/A` be a finite flat extension of domains
variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [IsDomain A] [IsDomain B] [Module.Finite A B] [Module.Flat A B]

-- Let `p` be a prime ideal of `A`
variable (p : Ideal A) [p.IsPrime]

-- Then there are finitely many prime ideals of `B` over `p`
noncomputable instance : Fintype (p.primesOver B) :=
  (Algebra.QuasiFinite.finite_primesOver p).fintype

-- And we have the formula `∑_q e_q * f_q = [B : A]`
#check Ideal.sum_ramification_inertia_eq_finrank p B

-- Let `q` be an ideal of `B`
variable (q : Ideal B)

-- The ramification index and inertia degree in mathlib
#check q.ramificationIdx B
#check q.inertiaDeg B

-- Let `G` be a finite Galois group for `B/A`
variable (G : Type*) [Group G] [Finite G]
  [MulSemiringAction G B] [IsGaloisGroup G A B]

-- Then `e * f * g = |G|`, where `g` is the number of primes over `p`
#check Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B G

end RamificationTheory
