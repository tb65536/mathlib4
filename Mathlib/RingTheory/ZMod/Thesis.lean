import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

open scoped NNReal

open scoped Pointwise

example {X : Type} {S : Set X} : Nonempty S ↔ S.Nonempty := by exact Set.nonempty_coe_sort

open Pointwise

lemma MapClusterPt.eq_of_eventually
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f g : Y → X} {y : Y}
    {ι : Type*} {F : Filter ι} {z : ι → Y}
    (h : MapClusterPt y F z) (ha : ContinuousAt f y) (hb : ContinuousAt g y)
    (hfg : f ∘ z =ᶠ[F] g ∘ z) : f y = g y := by
  refine tendsto_nhds_unique_of_frequently_eq ha hb ?_
  rw [Filter.eventuallyEq_iff_exists_mem] at hfg
  obtain ⟨s, hs1, hs2⟩ := hfg
  rw [mapClusterPt_def] at h
  have key : z '' s ∈ F.map z := Filter.image_mem_map hs1
  rw [clusterPt_iff_frequently] at h
  rw [frequently_nhds_iff]
  intro U hy hU
  specialize h U (hU.mem_nhds hy)
  rw [Filter.frequently_iff] at h
  specialize h key
  obtain ⟨T, hT1, hT2⟩ := h
  use T
  use hT2
  obtain ⟨i, hi, rfl⟩ := hT1
  apply hs2
  exact hi

theorem lem (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (χ : G → ℝ≥0)
    (C : Set (Set X))
    (hS0 : ∃ S0 ∈ C, Nonempty S0) -- If no such S0 exists, then topology on X is trivial by hC5
    (hC1 : ∀ g : G, ∀ S ∈ C, g • S ∈ C)
    (hC2: MeasureTheory.IsSetRing C)
    (hC3 : ∀ S ∈ C, IsCompact S)
    (hC4 : ∀ S ∈ C, IsOpen S)
    (hC5 : MeasurableSpace.generateFrom C = borel X)
    (μ : ∀ A : Finset C, A → NNReal)
    (hμ1 : ∀ A : Finset C, ∀ S : A, Nonempty S → 0 < μ A S)
    (hμ2 : ∀ A : Finset C, ∀ g : G, ∀ S T : A, g • (S : Set X) = (T : Set X) →
      μ A T = χ g * μ A S)
    (hμ3 : ∀ A : Finset C, ∀ S T U : A, Disjoint (S : Set X) (T : Set X) →
      (S : Set X) ∪ (T : Set X) = (U : Set X) → μ A U = μ A S + μ A T) :
    -- todo: add regularity condition
    ∃ μ : MeasureTheory.Measure X, μ ≠ 0 ∧ ∀ g : G, ∀ S : Set X, μ (g • S) = χ g * μ S := by
  obtain ⟨S0, hS0C, hS0⟩ := hS0
  let σ : Finset C → Set X → NNReal :=
    fun A S ↦ Function.extend (↑) (μ A) (0 : Set X → NNReal) S
  let τ : Finset C → Set X → ENNReal :=
    fun A S ↦ (σ A S0)⁻¹ * σ A S
  have hinj {A : Finset C} : Function.Injective ((↑) : A → Set X) := by
    intro x y h
    ext1
    ext1
    exact h
  have hτ0 : ∀ A : Finset C, τ A ∅ = 0 := by
    intro A
    dsimp only [τ, σ]
    by_cases h : ∃ S : A, S = (∅ : Set X)
    · obtain ⟨S, hS⟩ := h
      rw [← hS, hinj.extend_apply]
      have key := hμ3 A S S S ?_ ?_
      · rw [left_eq_add] at key
        rw [key, ENNReal.coe_zero, mul_zero]
      · rw [hS, disjoint_self, Set.bot_eq_empty]
      · rw [Set.union_self]
    · rw [Function.extend_apply' _ _ _ h, Pi.zero_apply, ENNReal.coe_zero, mul_zero]
  have hτ1 : ∀ A : Finset C, ⟨S0, hS0C⟩ ∈ A → τ A S0 = 1 := by
    intro A hS0A
    dsimp only [τ, σ]
    have h : ∃ T0 : A, T0 = S0 := ⟨⟨⟨S0, hS0C⟩, hS0A⟩, rfl⟩
    obtain ⟨T0, rfl⟩ := h
    rw [hinj.extend_apply, ← ENNReal.coe_mul, inv_mul_cancel₀, ENNReal.coe_one]
    exact (hμ1 A T0 hS0).ne'
  have hτ2 : ∀ A : Finset C, ∀ g : G, ∀ S : Set X, (hSC : S ∈ C) → ⟨S, hSC⟩ ∈ A →
      ⟨g • S, hC1 g S hSC⟩ ∈ A → τ A (g • S) = χ g * τ A S := by
    intro A g S hSC hSA hgSA
    dsimp only [τ, σ]
    by_cases h : ∃ T0 : A, T0 = S0
    · obtain ⟨T0, rfl⟩ := h
      rw [hinj.extend_apply]
      have h : ∃ gT : A, g • S = gT := ⟨⟨⟨g • S, hC1 g S hSC⟩, hgSA⟩, rfl⟩
      obtain ⟨gT, hgT⟩ := h
      rw [hgT]
      have h : ∃ T : A, T = S := ⟨⟨⟨S, hSC⟩, hSA⟩, rfl⟩
      obtain ⟨T, rfl⟩ := h
      rw [hinj.extend_apply, hinj.extend_apply, hμ2 A g T gT hgT, ← ENNReal.coe_mul,
        ← ENNReal.coe_mul, ← ENNReal.coe_mul, ENNReal.coe_inj]
      group
    · simp [Function.extend_apply' _ _ _ h]
  have hτ3 : ∀ A : Finset C, ∀ S T : Set X, Disjoint S T → (hSC : S ∈ C) → (hTC : T ∈ C) →
      ⟨S, hSC⟩ ∈ A → ⟨T, hTC⟩ ∈ A → ⟨S ∪ T, hC2.union_mem hSC hTC⟩ ∈ A →
      τ A (S ∪ T) = τ A S + τ A T := by
    intro A S T hST hSC hTC hSA hTA hSTA
    dsimp only [τ, σ]
    by_cases h : ∃ S0' : A, S0' = S0
    · obtain ⟨S0', rfl⟩ := h
      rw [hinj.extend_apply]
      have h : ∃ ST' : A, S ∪ T = ST' := ⟨⟨⟨S ∪ T, hC2.union_mem hSC hTC⟩, hSTA⟩, rfl⟩
      obtain ⟨ST', hST'⟩ := h
      rw [hST']
      have h : ∃ S' : A, S' = S := ⟨⟨⟨S, hSC⟩, hSA⟩, rfl⟩
      obtain ⟨S', rfl⟩ := h
      have h : ∃ T' : A, T' = T := ⟨⟨⟨T, hTC⟩, hTA⟩, rfl⟩
      obtain ⟨T', rfl⟩ := h
      rw [hinj.extend_apply, hinj.extend_apply, hinj.extend_apply,
        hμ3 A S' T' ST' hST hST', ← ENNReal.coe_mul, mul_add, ENNReal.coe_add,
        ENNReal.coe_mul, ENNReal.coe_mul]
    · simp [Function.extend_apply' _ _ _ h]
  have h : CompactSpace (Set X → ENNReal) := by
    infer_instance
  obtain ⟨μ, -, hμ⟩ := h.isCompact_univ.exists_mapClusterPt (f := Filter.atTop) (u := τ) (by simp)
  replace hμ0 : μ ∅ = 0 := by
    apply hμ.eq_of_eventually
    · exact (continuousAt_apply ∅ μ).tendsto
    · exact continuousAt_const.tendsto
    · rw [Filter.eventuallyEq_iff_exists_mem]
      use Set.univ
      use Filter.univ_mem
      intro A hA
      exact hτ0 A
  replace hμ1 : μ S0 = 1 := by
    apply hμ.eq_of_eventually
    · exact (continuousAt_apply S0 μ).tendsto
    · exact continuousAt_const.tendsto
    · rw [Filter.eventuallyEq_iff_exists_mem]
      use Set.Ici {⟨S0, hS0C⟩}
      use Filter.Ici_mem_atTop _
      intro A hA
      simp only [Set.mem_Ici, Finset.le_eq_subset, Finset.singleton_subset_iff] at hA
      exact hτ1 A hA
  replace hμ2 : ∀ g : G, ∀ S : Set X, S ∈ C → μ (g • S) = χ g * μ S := by
    intro g S hSC
    apply hμ.eq_of_eventually
    · exact continuousAt_apply (g • S) μ
    · refine ContinuousAt.comp' ?_ ?_
      · exact (ENNReal.continuous_const_mul ENNReal.coe_ne_top).continuousAt
      · exact continuousAt_apply S μ
    · rw [Filter.eventuallyEq_iff_exists_mem]
      classical
      use Set.Ici ({⟨S, hSC⟩, ⟨g • S, hC1 g S hSC⟩} : Finset C)
      use Filter.Ici_mem_atTop _
      intro A hA
      simp only [Set.mem_Ici, Finset.le_eq_subset, Finset.insert_subset_iff,
        Finset.singleton_subset_iff] at hA
      exact hτ2 A g S hSC hA.1 hA.2
  replace hμ3 : ∀ {S T : Set X}, S ∈ C → T ∈ C → Disjoint S T → μ (S ∪ T) = μ S + μ T := by
    intro S T hSC hTC hST
    apply hμ.eq_of_eventually
    · exact continuousAt_apply (S ∪ T) μ
    · exact ContinuousAt.add (continuousAt_apply S μ) (continuousAt_apply T μ)
    · rw [Filter.eventuallyEq_iff_exists_mem]
      classical
      use Set.Ici ({⟨S, hSC⟩, ⟨T, hTC⟩, ⟨S ∪ T, hC2.union_mem hSC hTC⟩} : Finset C)
      use Filter.Ici_mem_atTop _
      intro A hA
      simp only [Set.mem_Ici, Finset.le_eq_subset, Finset.insert_subset_iff,
        Finset.singleton_subset_iff] at hA
      exact hτ3 A S T hST hSC hTC hA.1 hA.2.1 hA.2.2
  let m := hC2.addContent_of_union μ hμ0 hμ3
  have hm : m.IsSigmaSubadditive := by
    apply MeasureTheory.isSigmaSubadditive_of_addContent_iUnion_eq_tsum hC2
    intro f hf1 hf2 hf3
    -- compact open trick
    sorry
  let τ := MeasureTheory.AddContent.measure m hC2.isSetSemiring
    (BorelSpace.measurable_eq.trans hC5.symm).le hm
  have hτ1 : τ S0 = 1 := by
    rwa [MeasureTheory.AddContent.measure_eq m hC2.isSetSemiring
      (BorelSpace.measurable_eq.trans hC5.symm) hm hS0C]
  replace hτ1 : τ ≠ 0 := by
    contrapose! hτ1
    simp [hτ1]
  have hτ2 : ∀ g : G, ∀ S : Set X, τ (g • S) = χ g * τ S := by
    -- dig into definition of τ
    sorry
  exact ⟨τ, hτ1, hτ2⟩
