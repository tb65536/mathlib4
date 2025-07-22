import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

open scoped NNReal

open scoped Pointwise

example {X : Type} {S : Set X} : Nonempty S ↔ S.Nonempty := by exact Set.nonempty_coe_sort

open Pointwise

theorem lem (G X : Type*) [Group G] [MulAction G X] [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (χ : G →* ℝ≥0) -- downgrade to function?
    (C : Set (Set X))
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
    ∃ μ : MeasureTheory.Measure X, μ ≠ 0 ∧ ∀ g : G, ∀ S : Set X, μ (g • S) = χ g * μ S := by -- Exists nonzero G-invariant Radon measure on X
  have hS0 : ∃ S0 ∈ C, Nonempty S0 := by
    simp only [Set.nonempty_coe_sort]
    by_contra! h
    rw [← Set.subset_singleton_iff] at h
    replace h := MeasurableSpace.generateFrom_mono h
    rw [hC5, MeasurableSpace.generateFrom_singleton_empty] at h
    -- should imply that the topology is trivial on X, in which theorem is trivial
    sorry
  obtain ⟨S0, hS0C, hS0⟩ := hS0
  let σ : Finset C → Set X → NNReal :=
    fun A S ↦ Function.extend (↑) (μ A) (0 : Set X → NNReal) S
  let τ : Finset C → Set X → NNReal :=
    fun A S ↦ (σ A S0)⁻¹ * σ A S
  have hinj {A : Finset C} : Function.Injective ((↑) : A → Set X) := by
    intro x y h
    ext1
    ext1
    exact h
  have hτ1 : ∀ A : Finset C, ⟨S0, hS0C⟩ ∈ A → τ A S0 = 1 := by
    intro A hS0A
    dsimp only [τ, σ]
    have h : ∃ T0 : A, T0 = S0 := ⟨⟨⟨S0, hS0C⟩, hS0A⟩, rfl⟩
    obtain ⟨T0, rfl⟩ := h
    rw [hinj.extend_apply, inv_mul_cancel₀]
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
      rw [hinj.extend_apply, hinj.extend_apply, hμ2 A g T gT hgT]
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
        hμ3 A S' T' ST' hST hST', mul_add]
    · simp [Function.extend_apply' _ _ _ h]


  -- have hτ3 : ∀ A : Set (Set X), (hA : A.Finite) → (hAC : A ⊆ C) → ∀ S T : Set X,
  --   Disjoint S T → (hSA : S ∈ A) → (hTA : T ∈ A) → (hSTA : S ∪ T ∈ A) →
  --     μ A hA hAC ⟨S ∪ T, hSTA⟩ = μ A hA hAC ⟨S, hSA⟩ + μ A hA hAC ⟨T, hTA⟩ := by
  --   sorry
  sorry
