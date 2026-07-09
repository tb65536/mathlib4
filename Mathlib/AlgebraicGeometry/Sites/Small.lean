/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Over
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.MorphismProperty.CommaSites
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Small sites

In this file we define the small sites associated to morphism properties and give
generating pretopologies.

## Main definitions

- `AlgebraicGeometry.Scheme.overGrothendieckTopology`: the Grothendieck topology on `Over S`
  obtained by localizing the topology on `Scheme` induced by `P` at `S`.
- `AlgebraicGeometry.Scheme.overPretopology`: the pretopology on `Over S` defined by
  `P`-coverings of `S`-schemes. The induced topology agrees with
  `AlgebraicGeometry.Scheme.overGrothendieckTopology`.
- `AlgebraicGeometry.Scheme.smallGrothendieckTopology`: the by the inclusion
  `P.Over ⊤ S ⥤ Over S` induced topology on `P.Over ⊤ S`.
- `AlgebraicGeometry.Scheme.smallPretopology`: the pretopology on `P.Over ⊤ S` defined by
  `P`-coverings of `S`-schemes with `P`. The induced topology agrees
  with `AlgebraicGeometry.Scheme.smallGrothendieckTopology`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P Q : MorphismProperty Scheme.{u}} {S : Scheme.{u}}

/-- The presieve defined by a `P`-cover of `S`-schemes. -/
@[deprecated "Use `𝒰.toPreZeroHypercover.presieve₀` instead. " (since := "2026-07-08")]
def Cover.toPresieveOver {X : Over S}
    (𝒰 : Precoverage.ZeroHypercover.{u} ((precoverage P).comap (Over.forget S)) X) :
    Presieve X :=
  𝒰.toPreZeroHypercover.presieve₀

/-- The presieve defined by a `P`-cover of `S`-schemes with `Q`. -/
def Cover.toPresieveOverProp {X : Q.Over ⊤ S}
    (𝒰 : Precoverage.ZeroHypercover.{u}
      (((precoverage P).comap (Over.forget S)).comap (MorphismProperty.Over.forget Q ⊤ S)) X) :
    Presieve X :=
  𝒰.toPreZeroHypercover.presieve₀

set_option backward.defeqAttrib.useBackward true in
lemma Cover.overEquiv_generate_toPresieveOver_eq_ofArrows {X : Over S}
    (𝒰 : Precoverage.ZeroHypercover.{u} ((precoverage P).comap (Over.forget S)) X) :
    Sieve.overEquiv X (Sieve.generate 𝒰.toPreZeroHypercover.presieve₀) =
      Sieve.ofArrows (fun i ↦ (𝒰.X i).left) (fun i ↦ (𝒰.f i).left) := by
  ext V f
  simp only [Sieve.overEquiv_iff, Sieve.generate_apply]
  constructor
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    exact ⟨(𝒰.X k).left, h.left, (𝒰.f k).left, ⟨k⟩, congrArg CommaMorphism.left hcomp⟩
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    have : (𝒰.f k).left ≫ X.hom = (𝒰.X k).hom := (𝒰.f k).w
    refine ⟨𝒰.X k, Over.homMk h (by simp [← hcomp, this]), 𝒰.f k, ⟨k⟩, ?_⟩
    ext : 1
    simpa

lemma Cover.toPresieveOver_le_arrows_iff {X : Over S} (R : Sieve X)
    (𝒰 : Precoverage.ZeroHypercover.{u} ((precoverage P).comap (Over.forget S)) X) :
    𝒰.toPreZeroHypercover.presieve₀ ≤ R.arrows ↔
      Presieve.ofArrows (fun i ↦ (𝒰.X i).left) (fun i ↦ (𝒰.f i).left) ≤
        (Sieve.overEquiv X R).arrows := by
  simp_rw [← Sieve.giGenerate.gc.le_iff_le, ← (Sieve.overEquiv X).map_rel_iff]
  rw [overEquiv_generate_toPresieveOver_eq_ofArrows]

variable [Q.IsStableUnderComposition]

private lemma foo (hPQ : P ≤ Q) (S : Scheme.{u}) {X : Q.Over ⊤ S} {R : Presieve ((MorphismProperty.Over.forget Q ⊤ S).obj X)}
    (H : R ∈ (Precoverage.over S (precoverage P)).coverings ((MorphismProperty.Over.forget Q ⊤ S).obj X)) :
    (R.functorPullback (MorphismProperty.Over.forget Q ⊤ S)).map (MorphismProperty.Over.forget Q ⊤ S) ∈
        ((precoverage P).over S).coverings ((MorphismProperty.Over.forget Q ⊤ S).obj X) := by
  have hle : precoverage P ≤ Q.precoverage :=
    fun _ _ hR _ _ hf ↦ hPQ _ (hR.2 hf)
  obtain ⟨T, rfl⟩ := MorphismProperty.exists_map_eq_of_presieve (precoverage P) hle H
  simpa using H

variable [P.IsMultiplicative] [P.RespectsIso]

variable [P.IsStableUnderBaseChange]

variable (P Q S)

/-- The pretopology on `Over S` induced by `P` where coverings are given by `P`-covers
of `S`-schemes. -/
abbrev overPretopology : Pretopology (Over S) :=
  ((Scheme.precoverage P).over S).toPretopology

/-- The topology on `Over S` induced from the topology on `Scheme` defined by `P`.
This agrees with the topology induced by `S.overPretopology P`, see
`AlgebraicGeometry.Scheme.overGrothendieckTopology_eq_toGrothendieck_overPretopology`. -/
abbrev overGrothendieckTopology : GrothendieckTopology (Over S) :=
  (Scheme.grothendieckTopology P).over S

lemma overGrothendieckTopology_eq_toGrothendieck_overPretopology :
    S.overGrothendieckTopology P = (S.overPretopology P).toGrothendieck := by
  rw [Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  exact over_toGrothendieck_eq_toGrothendieck_comap_forget (precoverage P) S

variable {S}

-- lemma mem_overGrothendieckTopology (X : Over S) (R : Sieve X) :
--     R ∈ S.overGrothendieckTopology P X ↔
--       ∃ (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S), 𝒰.toPresieveOver ≤ R.arrows := by
--   rw [overGrothendieckTopology_eq_toGrothendieck_overPretopology]
--   constructor
--   · rintro ⟨T, ⟨𝒰, h, rfl⟩, hle⟩
--     use 𝒰, h
--   · rintro ⟨𝒰, h𝒰, hle⟩
--     exact ⟨𝒰.toPresieveOver, ⟨𝒰, h𝒰, rfl⟩, hle⟩

variable (S) {P Q} in
lemma locallyCoverDense_of_le (hPQ : P ≤ Q) :
    (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) := by
  rw [overGrothendieckTopology_eq_toGrothendieck_overPretopology,
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  apply Precoverage.locallyCoverDense_of_map_functorPullback_mem
  apply foo hPQ

instance : (MorphismProperty.Over.forget P ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
  locallyCoverDense_of_le S le_rfl

variable (S) {Q} in
/-- If `P` and `Q` are morphism properties with `P ≤ Q`, this is the Grothendieck topology
induced via the forgetful functor `Q.Over ⊤ S ⥤ Over S` by the topology defined by `P`. -/
abbrev smallGrothendieckTopology : GrothendieckTopology (Q.Over ⊤ S) :=
  (MorphismProperty.Over.forget Q ⊤ S).restrictedTopology (S.overGrothendieckTopology P)

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE := smallGrothendieckTopology

variable [Q.IsStableUnderBaseChange] [Q.HasOfPostcompProperty Q]

/-- The pretopology defined on the subcategory of `S`-schemes satisfying `Q` where coverings
are given by `P`-coverings in `S`-schemes satisfying `Q`.
The most common case is `P = Q`. In this case, this is simply surjective families
in `S`-schemes with `P`. -/
abbrev smallPretopology : Pretopology (Q.Over ⊤ S) :=
  (((precoverage P).over S).comap (MorphismProperty.Over.forget Q ⊤ S)).toPretopology

variable (S) {P Q} in
lemma smallGrothendieckTopology_eq_toGrothendieck_smallPretopology (hPQ : P ≤ Q) :
    S.smallGrothendieckTopology P = (S.smallPretopology P Q).toGrothendieck := by
  rw [smallGrothendieckTopology, overGrothendieckTopology_eq_toGrothendieck_overPretopology,
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck,
    ← Precoverage.toGrothendieck_comap_eq_restrictedTopology]
  apply foo hPQ

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology :=
  smallGrothendieckTopology_eq_toGrothendieck_smallPretopology

variable {P Q}

lemma mem_toGrothendieck_smallPretopology (X : Q.Over ⊤ S) (R : Sieve X) :
    R ∈ (S.smallPretopology P Q).toGrothendieck X ↔
      ∀ x : X.left, ∃ (Y : Q.Over ⊤ S) (f : Y ⟶ X) (y : Y.left),
        R f ∧ P f.left ∧ f.left y = x := by
  rw [Pretopology.mem_toGrothendieck]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    intro x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    refine ⟨(𝒰.X (𝒰.idx x)).asOverProp S (p _), (𝒰.f (𝒰.idx x)).asOverProp S, y, hle _ _ ?_,
      𝒰.map_prop _, hy⟩
    use 𝒰.idx x
  · choose Y f y hf hP hy using h
    let 𝒰 : X.left.Cover (precoverage P) :=
      { I₀ := X.left,
        X := fun i ↦ (Y i).left
        f := fun i ↦ (f i).left
        mem₀ := by
          rw [presieve₀_mem_precoverage_iff]
          refine ⟨fun x ↦ ⟨x, y x, hy x⟩, hP⟩ }
    letI : 𝒰.Over S :=
      { over := fun i ↦ inferInstance
        isOver_map := fun i ↦ inferInstance }
    refine ⟨𝒰.toPresieveOverProp fun i ↦ MorphismProperty.Comma.prop _, ?_, ?_⟩
    · use 𝒰, inferInstance, fun i ↦ MorphismProperty.Comma.prop _
    · rintro - - ⟨i⟩
      exact hf i

lemma mem_smallGrothendieckTopology [P.HasOfPostcompProperty P] (X : P.Over ⊤ S) (R : Sieve X) :
    R ∈ S.smallGrothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S) (h : ∀ j, P (𝒰.X j ↘ S)),
          𝒰.toPresieveOverProp h ≤ R.arrows := by
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl]
  constructor
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    use 𝒰, h, p
  · rintro ⟨𝒰, h𝒰, p, hle⟩
    exact ⟨𝒰.toPresieveOverProp p, ⟨𝒰, h𝒰, p, rfl⟩, hle⟩

end AlgebraicGeometry.Scheme
