import Mathlib.GroupTheory.Sylow
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

open scoped NNReal Pointwise

/-- Type synonym for quotient topology. -/
def QuotientSpace (G X : Type*) [Group G] [MulAction G X] :=
  Quotient (MulAction.orbitRel G X)

def quotientMap (G X : Type*) [Group G] [MulAction G X] : X → QuotientSpace G X :=
  Quotient.mk (MulAction.orbitRel G X)

theorem quotientMap_surjective (G X : Type*) [Group G] [MulAction G X] :
    Function.Surjective (quotientMap G X) :=
  Quotient.mk_surjective

instance (G X : Type*) [Group G] [MulAction G X] [t : TopologicalSpace X] :
    TopologicalSpace (QuotientSpace G X) :=
  t.coinduced (quotientMap G X)

theorem quotientMap_isQuotientMap (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X] :
    Topology.IsQuotientMap (quotientMap G X) :=
  ⟨quotientMap_surjective G X, rfl⟩

structure OpenCovers (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X] where
  carrier : Set X
  carrier_open : IsOpen carrier
  carrier_precompact : IsCompact (closure carrier)
  carrier_covers : quotientMap G X '' carrier = Set.univ

@[ext]
theorem OpenCovers.ext {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
    {U V : OpenCovers G X} (h : U.carrier = V.carrier) : U = V := by
  cases U
  cases V
  congr

instance (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X] :
    PartialOrder (OpenCovers G X) :=
  { le := fun U V ↦ U.carrier = V.carrier ∨ closure U.carrier ≤ V.carrier
    le_refl := fun U ↦ Or.inl rfl
    le_trans := by
      rintro U V W (hUV | hUV) (hVW | hVW)
      · exact Or.inl (hUV.trans hVW)
      · exact Or.inr (hUV ▸ hVW)
      · exact Or.inr (hVW ▸ hUV)
      · exact Or.inr (hUV.trans ((subset_closure).trans hVW))
    le_antisymm := by
      rintro U V (hUV | hUV) (hVU | hVU) <;> ext1
      · exact hUV
      · exact hUV
      · exact hVU.symm
      · exact le_antisymm (subset_closure.trans hUV) (subset_closure.trans hVU) }

theorem tada {G : Type*} [Group G] {X : Type*} [MulAction G X] [TopologicalSpace X]
    [hc : CompactSpace (QuotientSpace G X)]
    [MeasurableSpace X] (μ : MeasureTheory.Measure X) (χ : G →* ℝ≥0)
    (hμ : ∀ S : Set X, ∀ g : G, μ (g • S) = χ g * μ S)
    (x₀ : X) :
    ∃ ν : MeasureTheory.Measure (MulAction.orbit G x₀),
      ∀ S : Set (MulAction.orbit G x₀), ∀ g : G, ν (g • S) = χ g * ν S := by
  let Q := QuotientSpace G X
  let π : X → Q := quotientMap G X
  let 𝓟 := OpenCovers G X
  obtain ⟨M, hM, -⟩ := IsChain.exists_maxChain (IsChain.empty : IsChain (α := 𝓟) LE.le ∅)



  sorry
