import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation41_implies_Equation334 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation334 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation334_implies_Equation41 (G : Type*) [Magma G] (h334 : Equation334 G) : Equation41 G := by
  have l0 : ∀ sK1 X1 X0 sK2 : G, (sK1 ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X1 X0 sK2
    conv => enter [1]; rw [h334 sK1 X1 X0]
    conv => enter [1, 2]; rw [h334 sK1 X0 sK2]
  have l1 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h334 X0 X1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← l0 sK1 X1 X0 X0]
  have l2 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h334 sK0 X1 X0]
    conv => enter [1, 2]; rw [h334 sK0 X0 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h334 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 X1 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h334 sK0 X0 sK0]
    conv => enter [1]; rw [l3 X0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h334 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l5 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation41_implies_Equation338 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation338 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK0]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 z x y]

@[equational_result]
theorem Equation338_implies_Equation41 (G : Type*) [Magma G] (h338 : Equation338 G) : Equation41 G := by
  have l0 : ∀ X1 sK2 X0 sK1 : G, (X1 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X1 sK2 X0 sK1
    conv => enter [1, 2]; rw [h338 sK2 X0 sK1]
    conv => enter [1]; rw [← h338 (sK1 ◇ sK2) X1 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h338 X0 X1 sK2]
    conv => enter [1]; rw [l0 X1 sK2 X0 sK1]
  have l2 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ X2) = ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [h338 X1 X2 X0]
    conv => enter [1]; rw [l1 X2 (X0 ◇ X1) sK1 sK2]
  have l3 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [l2 X1 X2 sK1 sK2 X1]
    conv => enter [1]; rw [← h338 X1 (sK1 ◇ sK2) X1]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l1 X0 sK2 sK1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [l3 X0 sK2 sK1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [← h338 sK2 X0 sK1]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [l1 sK2 X0 sK1 sK2]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l1 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2 X1]
  intro x y z
  conv => enter [1]; rw [l8 x x y z]

@[equational_result]
theorem Equation41_implies_Equation340 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation340 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation340_implies_Equation41 (G : Type*) [Magma G] (h340 : Equation340 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h340 X0 X1 X0]
    conv => enter [1]; rw [← h340 X2 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h340 X0 X1 sK0]
    conv => enter [1]; rw [h340 X1 (sK0 ◇ sK0) sK0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h340 X0 X1 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = (sK2 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [h340 sK1 sK2 X1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 (sK1 ◇ sK1) sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) (sK0 ◇ sK0) sK1 sK2]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [h340 (sK0 ◇ sK0) (sK1 ◇ sK2) sK0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [h340 sK0 sK0 X1]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) (sK0 ◇ sK0) sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [h340 (sK0 ◇ sK0) (sK1 ◇ sK2) sK0]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation341 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation341 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ sK0)]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w y]

@[equational_result]
theorem Equation341_implies_Equation41 (G : Type*) [Magma G] (h341 : Equation341 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h341 X0 X1 X0 X0]
    conv => enter [1]; rw [← h341 X2 X1 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h341 X0 X1 sK1 sK2]
    conv => enter [1]; rw [h341 X1 (sK1 ◇ sK2) sK1 sK2]
  have l2 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ sK2) = (sK2 ◇ (X1 ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [h341 sK1 sK2 X1 X2]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l1 sK2 (sK1 ◇ sK1) sK1 sK2]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h341 sK0 sK0 X1 X2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK1 sK2]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation41_implies_Equation342 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation342 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x z (x ◇ x)]

@[equational_result]
theorem Equation342_implies_Equation41 (G : Type*) [Magma G] (h342 : Equation342 G) : Equation41 G := by
  have l0 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h342 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h342 (sK0 ◇ sK0) X0 X1]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h342 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 X0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h342 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation344 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation344 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation344_implies_Equation41 (G : Type*) [Magma G] (h344 : Equation344 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h344 X0 X1 X0]
    conv => enter [1]; rw [← h344 X0 X2 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h344 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ sK0) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation345 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation345 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation345_implies_Equation41 (G : Type*) [Magma G] (h345 : Equation345 G) : Equation41 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h345 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← h345 sK1 X0 sK1 sK2]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h345 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X0) sK2]
  intro x y z
  conv => enter [1]; rw [l1 x x y z]

@[equational_result]
theorem Equation41_implies_Equation346 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation346 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation346_implies_Equation41 (G : Type*) [Magma G] (h346 : Equation346 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h346 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h346 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h346 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h346 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation348 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation348 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation348_implies_Equation41 (G : Type*) [Magma G] (h348 : Equation348 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h348 X0 X1 X0]
    conv => enter [1]; rw [← h348 X2 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h348 sK0 sK0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h348 X0 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = (X1 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [h348 sK1 sK2 X1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 (sK2 ◇ sK1) sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK0]
  intro x y z
  conv => enter [1]; rw [← l5 y z x]

@[equational_result]
theorem Equation41_implies_Equation349 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation349 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation349_implies_Equation41 (G : Type*) [Magma G] (h349 : Equation349 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h349 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h349 sK0 sK0 X1 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0 sK0]
    conv => enter [1]; rw [← h349 sK0 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation354 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation354 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation354_implies_Equation41 (G : Type*) [Magma G] (h354 : Equation354 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h354 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h354 sK0 X0 sK0 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h354 X0 X1 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 (X0 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation356 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation356 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK3)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation356_implies_Equation41 (G : Type*) [Magma G] (h356 : Equation356 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h356 X0 X1 X0 X0]
    conv => enter [1]; rw [← h356 X2 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation357 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation357 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK3 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK3
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK0)]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation357_implies_Equation41 (G : Type*) [Magma G] (h357 : Equation357 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h357 X0 X1 X0 X0]
    conv => enter [1]; rw [← h357 X2 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation358 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation358 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ sK0)]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation358_implies_Equation41 (G : Type*) [Magma G] (h358 : Equation358 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h358 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h358 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation352 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation352 G := by
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [h41 z z (z ◇ z)]

@[equational_result]
theorem Equation352_implies_Equation41 (G : Type*) [Magma G] (h352 : Equation352 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h352 X0 X1 X0]
    conv => enter [1]; rw [← h352 X3 X4 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation350 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation350 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation350_implies_Equation41 (G : Type*) [Magma G] (h350 : Equation350 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h350 X0 X1 X0]
    conv => enter [1]; rw [← h350 X0 X3 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h350 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X0) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation337 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation337 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

@[equational_result]
theorem Equation337_implies_Equation41 (G : Type*) [Magma G] (h337 : Equation337 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h337 X0 X1 X0]
    conv => enter [1]; rw [← h337 X3 X1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h337 sK1 sK2 X0]
  have l2 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h337 X1 X0 sK2]
    conv => enter [1, 2]; rw [l0 X0 sK2 sK1]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1]; rw [l2 sK2 (sK1 ◇ sK2) sK1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l0 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK2]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l2 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 sK2 X1]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation353 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation353 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l0 z w x y]

@[equational_result]
theorem Equation353_implies_Equation41 (G : Type*) [Magma G] (h353 : Equation353 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h353 X0 X1 X0 X0]
    conv => enter [1]; rw [← h353 X4 X5 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3344 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3344 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation3344_4512_implies_Equation41 (G : Type*) [Magma G] (h3344 : Equation3344 G) (h4512 : Equation4512 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h3344 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3344 X0 X0 X0]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 2]; rw [← h3344 X0 (X0 ◇ (X0 ◇ X1)) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l0 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3344 X0 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h3344 X0 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1]; rw [← l5 X0 (X1 ◇ X2)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) X0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l8 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 X0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [l10 X0 sK0]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h3344 (sK0 ◇ sK0) X1 X0]
    conv => enter [1, 2]; rw [← l11 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l12 sK0 X1 X0]
    conv => enter [1]; rw [← l8 X1 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l14 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l8 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK0 X1 X0]
  have l15 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l14 sK1 sK2 sK0]
    conv => enter [1]; rw [l14 (sK0 ◇ sK0) sK1 sK0]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l16 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

@[equational_result]
theorem Equation41_implies_Equation3347 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3347 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation3347_4512_implies_Equation41 (G : Type*) [Magma G] (h3347 : Equation3347 G) (h4512 : Equation4512 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h3347 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h3347 X0 X1 X1]
  have l1 : ∀ X0 sK0 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 (X0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← h3347 X0 sK0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3347 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h3347 X1 X1 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [← l1 X0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3347 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l6 sK0 X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation3348 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3348 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK0]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK2 ◇ sK0))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 z x y]

theorem Equation3348_4512_implies_Equation41 (G : Type*) [Magma G] (h3348 : Equation3348 G) (h4512 : Equation4512 G) : Equation41 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h3348 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2]; rw [← h3348 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h3348 X0 X2 X1]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3348 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h3348 (sK0 ◇ sK0) X0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3348 sK0 X0 sK0]
    conv => enter [1]; rw [l2 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3348 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l3 sK0 (X0 ◇ (X1 ◇ X0))]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0 X0]
    conv => enter [1]; rw [← h3348 X0 sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3348 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l5 X0 sK0]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((X0 ◇ sK0) ◇ X1) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l1 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l5 X0 sK0]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X1 ◇ (X3 ◇ X0)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l1 X3 X0 (X1 ◇ (X2 ◇ X1))]
    conv => enter [1]; rw [← h3348 X1 (X3 ◇ X0) X2]
  have l10 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = (X1 ◇ (X3 ◇ X0)) := by
    intro X1 X0 X3
    conv => enter [1]; rw [h3348 X1 X0 X1]
    conv => enter [1]; rw [l9 X0 X1 X1 X3]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l8 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK0]
    conv => enter [1]; rw [← l11 sK0 X1 X0]
  have l13 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h3348 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 (sK1 ◇ sK2)]
  have l14 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [h3348 X0 sK2 X1]
    conv => enter [1]; rw [← l1 sK1 sK2 (X0 ◇ (X1 ◇ X0))]
  have l15 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l14 X0 sK2 sK1 X0]
    conv => enter [1]; rw [← h3348 X0 (sK1 ◇ sK2) X0]
  have l16 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l13 sK2 X0 sK1]
    conv => enter [1]; rw [← l10 X0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l17 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l12 sK2 X0 sK0]
    conv => enter [1]; rw [l16 sK2 X0 sK1]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK1]
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ sK2) sK0]
  have l19 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ sK2)]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0 sK0 sK1 sK2]
  have l21 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK0]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK0]
    conv => enter [1]; rw [← l21 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l22 x y z]

@[equational_result]
theorem Equation41_implies_Equation3351 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3351 G := by
  have l0 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK2 (sK1 ◇ (sK3 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w y x]

@[equational_result]
theorem Equation3351_implies_Equation41 (G : Type*) [Magma G] (h3351 : Equation3351 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3351 X1 X2 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h3351 X0 X1 X1 X1]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3351 X0 X1 sK0 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) X1 X0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3351 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l0 (sK1 ◇ sK2) X1 X0]
  have l3 : ∀ sK0 X0 X1 X2 X3 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ X3) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1]; rw [← l1 X3 (X0 ◇ (X1 ◇ X2)) sK0]
    conv => enter [1]; rw [← h3351 X0 X3 X1 X2]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK1) sK2 sK1 sK2]
  have l5 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ X3) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h3351 X0 (sK0 ◇ sK0) X0 X0]
    conv => enter [1]; rw [l3 sK0 X0 X0 X0 X3]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [← l2 X0 sK2 sK1 sK2]
  have l7 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← l5 X0 sK0 sK2]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [← l5 X0 X0 X1]
    conv => enter [1]; rw [← l7 sK1 sK2 X0 X0]
  intro x y z
  conv => enter [1]; rw [l8 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3362 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3362 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x y (z ◇ (x ◇ x))]

theorem Equation3362_4512_implies_Equation41 (G : Type*) [Magma G] (h3362 : Equation3362 G) (h4512 : Equation4512 G) : Equation41 G := by
  have l0 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h3362 (X1 ◇ (X0 ◇ X0)) X2 X3]
    conv => enter [1, 2, 2]; rw [← h3362 X0 (X1 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h3362 (X0 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h3362 X0 X1 (X0 ◇ X0)]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l1 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l3 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l0 X1 X0 X2 X3]
    conv => enter [1, 2, 2]; rw [← h3362 X0 X0 X1]
  have l4 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2 X1]
    conv => enter [1]; rw [← h3362 X0 X2 X1]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l4 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l2 X1 X0 (X0 ◇ X2)]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X0]
    conv => enter [1]; rw [← l7 X0 X2 X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h3362 sK0 X0 X0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1]; rw [l9 sK1 sK1 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK0 sK1 sK0]
    conv => enter [1]; rw [← l10 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation41_implies_Equation3365 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3365 G := by
  have l0 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z x w y]

@[equational_result]
theorem Equation3365_implies_Equation41 (G : Type*) [Magma G] (h3365 : Equation3365 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3365 X2 X3 X1 (X0 ◇ X2)]
    conv => enter [1, 2]; rw [← h3365 X0 X1 X2 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3365 X0 X1 X0 X0]
    conv => enter [1]; rw [← l0 X2 X1 X0 (X0 ◇ X0)]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ sK2) sK0 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK0 sK1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← l0 X0 (sK1 ◇ sK2) sK1 sK1]
  have l6 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK2) X0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

@[equational_result]
theorem Equation41_implies_Equation3366 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3366 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l0 z y x]

theorem Equation3366_4512_implies_Equation41 (G : Type*) [Magma G] (h3366 : Equation3366 G) (h4512 : Equation4512 G) : Equation41 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3366 sK0 sK0 X0]
    conv => enter [1]; rw [← h3366 (sK0 ◇ sK0) X0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3366 (X0 ◇ (sK0 ◇ sK0)) sK0 X1]
    conv => enter [1, 2, 2]; rw [← h3366 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3366 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3366 sK0 sK0 X0]
    conv => enter [1, 2]; rw [l0 X0 sK0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h3366 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l6 X0 X1 sK0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h3366 X0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← l9 sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h3366 sK0 X0 X1]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0 sK0]
    conv => enter [1]; rw [l12 X0 sK0 sK0]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3366 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 (X1 ◇ X0)]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l14 X0 X1 sK0]
    conv => enter [1]; rw [← l11 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l15 y z x]

@[equational_result]
theorem Equation41_implies_Equation3368 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3368 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ sK2))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l0 z y]

theorem Equation3368_4512_implies_Equation41 (G : Type*) [Magma G] (h3368 : Equation3368 G) (h4512 : Equation4512 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3368 X0 X1 X0]
    conv => enter [1]; rw [← h3368 X2 X1 X0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3368 X1 sK0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3368 X1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h3368 X0 sK0 sK0]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l2 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 X0]
  have l5 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0
    conv => enter [1]; rw [l3 X1 sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 sK0 sK0]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ sK0) := by
    intro sK0 X1
    conv => enter [1, 2]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 X1 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l6 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3368 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK0]
    conv => enter [1]; rw [← l8 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation3369 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3369 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK2 ◇ sK0))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z y w]

@[equational_result]
theorem Equation3369_implies_Equation41 (G : Type*) [Magma G] (h3369 : Equation3369 G) : Equation41 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ X3) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h3369 X0 X1 X3 X3]
    conv => enter [1]; rw [← h3369 X2 X3 X1 (X1 ◇ X3)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3369 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3369 X2 X1 X0 X0]
  have l2 : ∀ X2 X0 sK0 : G, (X2 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X2 X0 sK0
    conv => enter [1]; rw [← l0 X0 X2 sK0 X2]
    conv => enter [1, 2]; rw [l1 X2 sK0 sK0]
  have l3 : ∀ X2 X0 sK1 sK2 : G, (X2 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X2 X0 sK1 sK2
    conv => enter [1]; rw [← l0 X0 X2 sK2 X2]
    conv => enter [1, 2]; rw [l1 X2 sK2 sK1]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK2 (sK0 ◇ sK0) sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [l3 (sK1 ◇ sK1) (sK1 ◇ sK2) sK1 sK2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← l8 sK0 X1]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK2) sK0]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 (sK1 ◇ sK2) (sK0 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation3372 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3372 G := by
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [h41 z y (z ◇ (z ◇ z))]

@[equational_result]
theorem Equation3372_implies_Equation41 (G : Type*) [Magma G] (h3372 : Equation3372 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3372 X0 X1 X0]
    conv => enter [1]; rw [← h3372 X2 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3372 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3372 sK1 sK2 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [h3372 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation3373 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3373 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK3 ◇ sK0))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z w y]

@[equational_result]
theorem Equation3373_implies_Equation41 (G : Type*) [Magma G] (h3373 : Equation3373 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3373 X2 X3 X1 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h3373 X0 X1 X1 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3373 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3373 X2 X1 X0 X0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK0]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 X0 sK2]
    conv => enter [1, 2]; rw [l1 X0 sK2 sK1]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK2 (sK0 ◇ sK0) sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [l3 (sK1 ◇ sK1) (sK1 ◇ sK2) sK1 sK2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← l8 sK0 X1]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK2) sK0]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 (sK1 ◇ sK2) (sK0 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation3374 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3374 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w x y]

@[equational_result]
theorem Equation3374_implies_Equation41 (G : Type*) [Magma G] (h3374 : Equation3374 G) : Equation41 G := by
  have l0 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X1 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h3374 (sK1 ◇ sK2) X1 X0 sK1]
    conv => enter [1, 2]; rw [← h3374 sK2 X0 sK1 sK1]
  have l1 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ X0) = (X1 ◇ X0) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X0 (sK1 ◇ X1)]
    conv => enter [1]; rw [← h3374 X1 X0 sK2 sK1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X0 X0 X1 X0]
    conv => enter [1]; rw [l1 X0 X0 X1 X2]
  have l3 : ∀ X2 X3 sK1 sK2 X0 X1 : G, (X2 ◇ X3) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X3 sK1 sK2 X0 X1
    conv => enter [1]; rw [h3374 X2 X3 X0 X1]
    conv => enter [1]; rw [← l1 sK1 sK2 (X0 ◇ (X1 ◇ X2)) X3]
  have l4 : ∀ X2 X3 sK1 sK2 : G, (X2 ◇ X3) = (X2 ◇ (sK1 ◇ sK2)) := by
    intro X2 X3 sK1 sK2
    conv => enter [1]; rw [l3 X2 X3 sK1 sK2 X2 X2]
    conv => enter [1]; rw [← h3374 X2 (sK1 ◇ sK2) X2 X2]
  have l5 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
    conv => enter [1]; rw [← h3374 sK0 X2 X1 sK0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [l4 X0 sK2 sK1 sK2]
  have l7 : ∀ X0 sK1 sK2 sK0 X2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ X2) := by
    intro X0 sK1 sK2 sK0 X2
    conv => enter [1]; rw [l4 X0 (sK1 ◇ sK2) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 X0 X0 sK0 X2]
  have l8 : ∀ sK1 sK2 sK0 X2 : G, (sK1 ◇ sK2) = (sK0 ◇ X2) := by
    intro sK1 sK2 sK0 X2
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK1 sK2 sK0 X2]
  intro x y z
  conv => enter [1]; rw [l8 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3376 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3376 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK3)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ sK3))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK3)]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w y]

@[equational_result]
theorem Equation3376_implies_Equation41 (G : Type*) [Magma G] (h3376 : Equation3376 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3376 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3376 X2 X1 X0 X0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3376 sK0 sK0 sK2 sK1]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3376 sK1 sK2 sK2 sK1]
  have l3 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK0 (sK2 ◇ (sK1 ◇ sK2)) X0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [← l3 sK0 sK2 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

@[equational_result]
theorem Equation41_implies_Equation3377 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3377 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK3
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z w y]

@[equational_result]
theorem Equation3377_implies_Equation41 (G : Type*) [Magma G] (h3377 : Equation3377 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3377 X2 X3 X1 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h3377 X0 X1 (X2 ◇ X2) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3377 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3377 X2 X1 X0 X0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK0]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 X0 sK2]
    conv => enter [1, 2]; rw [l1 X0 sK2 sK1]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK2 (sK0 ◇ sK0) sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [l3 (sK1 ◇ sK1) (sK1 ◇ sK2) sK1 sK2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← l8 sK0 X1]
  have l11 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l9 sK1 sK2 sK1]
    conv => enter [1]; rw [h3377 sK1 (sK1 ◇ sK2) X1 X2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l10 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK1)) sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation3378 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3378 G := by
  have l0 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ sK0)]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]
  conv => enter [1]; rw [l0 z w u y]

@[equational_result]
theorem Equation3378_implies_Equation41 (G : Type*) [Magma G] (h3378 : Equation3378 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3378 X2 X3 X1 X2 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h3378 X0 X1 X2 X2 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3378 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3378 X2 X1 X0 X0 X0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK0]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 X0 sK2]
    conv => enter [1, 2]; rw [l1 X0 sK2 sK1]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK2 (sK0 ◇ sK0) sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [l3 (sK1 ◇ sK1) (sK1 ◇ sK2) sK1 sK2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← l8 sK0 X1]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK2) sK0]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 (sK1 ◇ sK2) (sK0 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation3379 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3379 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x z (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation3379_implies_Equation41 (G : Type*) [Magma G] (h3379 : Equation3379 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3379 X0 X1 X0]
    conv => enter [1]; rw [← h3379 X0 X2 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h3379 sK0 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation41_implies_Equation3381 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3381 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation3381_implies_Equation41 (G : Type*) [Magma G] (h3381 : Equation3381 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3381 X0 X1 X0]
    conv => enter [1]; rw [← h3381 X0 X2 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3381 X0 X1 sK1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ sK1)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3381 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ sK0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3382 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3382 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3382_implies_Equation41 (G : Type*) [Magma G] (h3382 : Equation3382 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3382 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3382 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3382 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3382 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3383 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3383 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation3383_4512_implies_Equation41 (G : Type*) [Magma G] (h3383 : Equation3383 G) (h4512 : Equation4512 G) : Equation41 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h3383 (X1 ◇ X0) X0 X2]
    conv => enter [1, 2]; rw [← h3383 X0 X1 (X1 ◇ X0)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3383 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [← h3383 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h3383 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3383 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2]; rw [← l2 sK0 X0]
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [← l1 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l4 sK0 X0 X1]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 sK0 X0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3383 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ (X1 ◇ X0))]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3383 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l8 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation3386 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3386 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3386_implies_Equation41 (G : Type*) [Magma G] (h3386 : Equation3386 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h3386 X2 X0 X3 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h3386 X0 X1 X2 X2]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l0 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK0 X1 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l1 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation3387 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3387 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation3387_implies_Equation41 (G : Type*) [Magma G] (h3387 : Equation3387 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3387 X0 X1 X0]
    conv => enter [1]; rw [← h3387 X0 X2 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3387 X0 X1 sK1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3387 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3389 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3389 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41 sK2 sK0 (sK2 ◇ sK2)]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z x]

@[equational_result]
theorem Equation3389_implies_Equation41 (G : Type*) [Magma G] (h3389 : Equation3389 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3389 X0 X1 X0]
    conv => enter [1]; rw [← h3389 X0 X2 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3389 X0 X1 sK1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ sK1)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3389 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ sK0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3390 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3390 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3390_implies_Equation41 (G : Type*) [Magma G] (h3390 : Equation3390 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3390 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3390 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3390 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3390 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3391 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3391 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation3391_implies_Equation41 (G : Type*) [Magma G] (h3391 : Equation3391 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3391 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3391 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3391 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3391 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3393 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3393 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK3)]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation3393_implies_Equation41 (G : Type*) [Magma G] (h3393 : Equation3393 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3393 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3393 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3393 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ sK1)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3393 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ sK0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3394 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3394 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h41 sK0 sK3 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation3394_implies_Equation41 (G : Type*) [Magma G] (h3394 : Equation3394 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3394 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3394 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3394 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3394 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3395 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3395 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK1 ◇ sK0)]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

@[equational_result]
theorem Equation3395_implies_Equation41 (G : Type*) [Magma G] (h3395 : Equation3395 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3395 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3395 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3395 X0 X1 sK1 X0 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3395 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3396 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3396 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x z (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation3396_implies_Equation41 (G : Type*) [Magma G] (h3396 : Equation3396 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3396 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h3396 sK0 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h3396 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3396 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation3399 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3399 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3399_implies_Equation41 (G : Type*) [Magma G] (h3399 : Equation3399 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X3 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h3399 X1 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3399 X0 X1 X2 X1]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0 sK0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3399 X0 X1 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation3400 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3400 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation3400_implies_Equation41 (G : Type*) [Magma G] (h3400 : Equation3400 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3400 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [← h3400 sK0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X1]
  have l2 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h3400 (sK0 ◇ sK0) X1 X2]
    conv => enter [1, 2, 2]; rw [l1 X1 sK0 X0]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h3400 sK0 sK0 X1]
    conv => enter [1, 2]; rw [l1 sK0 sK0 X0]
  have l4 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l2 sK0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X1 sK0]
  have l5 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ X2) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h3400 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0 (X2 ◇ (X2 ◇ X1)) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3400 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l5 X1 X2 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

@[equational_result]
theorem Equation41_implies_Equation3402 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3402 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation3402_implies_Equation41 (G : Type*) [Magma G] (h3402 : Equation3402 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3402 X0 X1 X0]
    conv => enter [1]; rw [← h3402 X2 X1 X0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3402 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3402 X0 sK0 sK0]
  have l2 : ∀ X1 sK0 : G, (X1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l1 X1 sK0 X1]
    conv => enter [1, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3402 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 X1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

@[equational_result]
theorem Equation41_implies_Equation3403 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3403 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3403_implies_Equation41 (G : Type*) [Magma G] (h3403 : Equation3403 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3403 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3403 X2 X1 X0 X0]
  have l1 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ sK0) = (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [h3403 X1 sK0 X2 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X2 X0 : G, (sK0 ◇ sK0) = (X2 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l1 sK0 sK0 X2 X0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h3403 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK0 X1 X1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation41_implies_Equation3406 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3406 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK2)]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z y]

@[equational_result]
theorem Equation3406_implies_Equation41 (G : Type*) [Magma G] (h3406 : Equation3406 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3406 X0 X1 X0]
    conv => enter [1]; rw [← h3406 X2 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3406 X0 X1 sK0]
    conv => enter [1, 2]; rw [h3406 X1 (sK0 ◇ sK0) sK0]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3406 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3406 X0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [h3406 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) X1]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3406 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 X1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [← l7 sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation3407 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3407 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3407_implies_Equation41 (G : Type*) [Magma G] (h3407 : Equation3407 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3407 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3407 X2 X1 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3407 sK0 sK0 sK1 sK2]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3407 sK1 sK2 sK1 sK2]
  have l3 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

@[equational_result]
theorem Equation41_implies_Equation3408 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3408 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation3408_implies_Equation41 (G : Type*) [Magma G] (h3408 : Equation3408 G) : Equation41 G := by
  have l0 : ∀ sK1 sK2 X1 X2 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [h3408 (sK1 ◇ sK2) X1 X2 X0]
    conv => enter [1, 2]; rw [← h3408 sK2 X0 X1 sK1]
  have l1 : ∀ X3 X0 sK2 X1 X2 sK1 : G, (X3 ◇ (X0 ◇ (sK2 ◇ X1))) = (X2 ◇ (sK1 ◇ sK2)) := by
    intro X3 X0 sK2 X1 X2 sK1
    conv => enter [1, 2]; rw [← l0 sK1 sK2 (X3 ◇ X2) X0 X1]
    conv => enter [1]; rw [← h3408 X2 (sK1 ◇ sK2) X3 X3]
  have l2 : ∀ X2 sK1 sK2 X1 X0 : G, (X2 ◇ (sK1 ◇ sK2)) = (X1 ◇ X0) := by
    intro X2 sK1 sK2 X1 X0
    conv => enter [1]; rw [← l1 X2 X0 sK2 X1 X2 sK1]
    conv => enter [1]; rw [← h3408 X1 X0 X2 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l2 sK1 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3410 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3410 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK3)]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation3410_implies_Equation41 (G : Type*) [Magma G] (h3410 : Equation3410 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3410 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3410 X2 X1 X0 X0]
  have l1 : ∀ X2 sK2 sK1 X0 X1 : G, (X2 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro X2 sK2 sK1 X0 X1
    conv => enter [1]; rw [h3410 X2 sK2 (sK1 ◇ sK2) X1]
    conv => enter [1, 2]; rw [← h3410 X0 X1 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1 X0 X1]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3410 X0 X1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l2 sK1 sK2 X1 (X0 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l3 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3411 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3411 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation3411_implies_Equation41 (G : Type*) [Magma G] (h3411 : Equation3411 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3411 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3411 X2 X1 X0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3411 sK0 sK0 X0 sK0]
  have l2 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h3411 sK1 sK2 X0 sK0]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ sK2) = (X1 ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [h3411 sK1 (sK2 ◇ (sK0 ◇ sK0)) X1 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK2 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [← l5 y z x]

@[equational_result]
theorem Equation41_implies_Equation3412 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3412 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK1 ◇ sK0)]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

@[equational_result]
theorem Equation3412_implies_Equation41 (G : Type*) [Magma G] (h3412 : Equation3412 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h3412 X2 X3 X4 X1 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h3412 X0 X1 X3 X2 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3412 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3412 X2 X1 X0 X0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ sK0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← l0 X0 sK0 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0 sK0]
  have l3 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ sK2) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [← l0 X0 sK2 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK2 sK1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 sK1 sK1 sK1 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

@[equational_result]
theorem Equation41_implies_Equation3430 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3430 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h41 sK1 sK3 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x z w]

@[equational_result]
theorem Equation3430_implies_Equation41 (G : Type*) [Magma G] (h3430 : Equation3430 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3430 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3430 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h3430 sK0 sK0 X0 X0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation3432 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3432 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK3]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3432_implies_Equation41 (G : Type*) [Magma G] (h3432 : Equation3432 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3432 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3432 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3432 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ sK1)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3432 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ sK0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3433 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3433 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3433_implies_Equation41 (G : Type*) [Magma G] (h3433 : Equation3433 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3433 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3433 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3433 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3433 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3434 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3434 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation3434_implies_Equation41 (G : Type*) [Magma G] (h3434 : Equation3434 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3434 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3434 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3434 X0 X1 sK1 X0 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3434 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3435 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3435 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3435_implies_Equation41 (G : Type*) [Magma G] (h3435 : Equation3435 G) : Equation41 G := by
  have l0 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h3435 sK0 sK0 X1 X0]
    conv => enter [1]; rw [← h3435 (sK0 ◇ sK0) X0 X1 X1]
  have l1 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ X2) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h3435 X1 X2 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l0 X0 sK0 (X1 ◇ (X2 ◇ X1))]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3435 sK0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l0 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l1 X1 X2 X1 sK0]
    conv => enter [1]; rw [← l2 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3437 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3437 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK3]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3437_implies_Equation41 (G : Type*) [Magma G] (h3437 : Equation3437 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3437 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3437 X2 X1 X0 X0]
  have l1 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ sK0) = (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [h3437 X2 sK0 sK0 X2]
    conv => enter [1, 2]; rw [h3437 X2 (sK0 ◇ sK0) X0 X1]
  have l2 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h3437 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h3437 X0 sK0 sK0 X2]
  have l3 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ sK0) = (X2 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [h3437 X0 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l4 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l3 sK0 sK0 X2 X1]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l2 X1 X2 sK0 X1]
    conv => enter [1, 2]; rw [l0 X1 sK0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 X0 X1]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l9 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h3437 X0 X1 (sK0 ◇ sK0) X2]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0 X0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0) X0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation3438 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3438 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3438_implies_Equation41 (G : Type*) [Magma G] (h3438 : Equation3438 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h3438 X2 X3 X4 (X1 ◇ X3)]
    conv => enter [1, 2]; rw [← h3438 X0 X1 (X1 ◇ X3) X3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3438 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3438 X2 X1 X0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ sK0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← l0 X0 sK0 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0 sK0]
  have l3 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ sK2) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [← l0 X0 sK2 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK2 sK1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 sK1 sK1 sK1 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

@[equational_result]
theorem Equation41_implies_Equation3439 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3439 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation3439_implies_Equation41 (G : Type*) [Magma G] (h3439 : Equation3439 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h3439 X2 X3 X4 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h3439 X0 X1 X2 X3 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3439 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3439 X2 X1 X0 X0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ sK0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← l0 X0 sK0 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK0 sK0]
  have l3 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK1 ◇ sK2) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [← l0 X0 sK2 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK2 sK1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 sK1 sK1 sK1 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

@[equational_result]
theorem Equation41_implies_Equation3440 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3440 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK1]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3440_implies_Equation41 (G : Type*) [Magma G] (h3440 : Equation3440 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3440 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3440 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3440 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3440 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3442 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3442 G := by
  have l0 : ∀ sK3 sK0 : G, (sK3 ◇ sK3) = (sK0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [h41 sK3 sK0 (sK3 ◇ sK3)]
  have l1 : ∀ sK3 sK0 : G, (sK3 ◇ sK3) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h41 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z w]

@[equational_result]
theorem Equation3442_implies_Equation41 (G : Type*) [Magma G] (h3442 : Equation3442 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3442 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3442 X2 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3443 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3443 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3443_implies_Equation41 (G : Type*) [Magma G] (h3443 : Equation3443 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3443 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3443 X2 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3444 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3444 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ sK0) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 sK0]
  have l2 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK4 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation3444_implies_Equation41 (G : Type*) [Magma G] (h3444 : Equation3444 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3444 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h3444 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3445 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3445 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation3445_implies_Equation41 (G : Type*) [Magma G] (h3445 : Equation3445 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3445 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3445 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3445 X0 X1 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3445 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3447 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3447 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ (sK0 ◇ sK3))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation3447_implies_Equation41 (G : Type*) [Magma G] (h3447 : Equation3447 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3447 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3447 X2 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3448 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3448 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [h41 sK0 sK3 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3448_implies_Equation41 (G : Type*) [Magma G] (h3448 : Equation3448 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3448 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3448 X2 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3449 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3449 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation3449_implies_Equation41 (G : Type*) [Magma G] (h3449 : Equation3449 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3449 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h3449 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3450 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3450 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ sK2))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation3450_implies_Equation41 (G : Type*) [Magma G] (h3450 : Equation3450 G) : Equation41 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h3450 X0 X2 X0 X0 X0]
    conv => enter [1]; rw [← h3450 X0 X1 X0 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3450 X0 X1 sK1 X0 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3450 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3452 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3452 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ sK4))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation3452_implies_Equation41 (G : Type*) [Magma G] (h3452 : Equation3452 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3452 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h3452 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3453 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3453 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ (sK0 ◇ sK1))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation3453_implies_Equation41 (G : Type*) [Magma G] (h3453 : Equation3453 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3453 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h3453 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3454 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3454 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ sK0) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [h41 sK0 sK4 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

@[equational_result]
theorem Equation3454_implies_Equation41 (G : Type*) [Magma G] (h3454 : Equation3454 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3454 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h3454 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3455 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3455 G := by
  have l0 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK5 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y z w u v]

@[equational_result]
theorem Equation3455_implies_Equation41 (G : Type*) [Magma G] (h3455 : Equation3455 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3455 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h3455 X2 X3 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3423 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3423 G := by
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [h41 z z (z ◇ (z ◇ z))]

@[equational_result]
theorem Equation3423_implies_Equation41 (G : Type*) [Magma G] (h3423 : Equation3423 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h3423 X0 X1 X0]
    conv => enter [1]; rw [← h3423 X3 X4 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3421 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3421 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation3421_implies_Equation41 (G : Type*) [Magma G] (h3421 : Equation3421 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3421 X0 X1 X0]
    conv => enter [1]; rw [← h3421 X0 X3 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3421 X0 X1 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ X0)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3421 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ X0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3357 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3357 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

@[equational_result]
theorem Equation3357_implies_Equation41 (G : Type*) [Magma G] (h3357 : Equation3357 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3357 X0 X1 X0]
    conv => enter [1]; rw [← h3357 X3 X1 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3357 X0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l2 sK0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3357 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l7 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3357 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0 X0 X0]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l7 X1 X0 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation3424 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3424 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l0 z w x y]

@[equational_result]
theorem Equation3424_implies_Equation41 (G : Type*) [Magma G] (h3424 : Equation3424 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h3424 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3424 X4 X5 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3415 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3415 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation3415_implies_Equation41 (G : Type*) [Magma G] (h3415 : Equation3415 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3415 X0 X1 X0]
    conv => enter [1]; rw [← h3415 X0 X3 X0]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3415 X0 X1 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (X0 ◇ sK1)) sK2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3415 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X0 ◇ sK0)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3419 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3419 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK0]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK0]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]
  conv => enter [1]; rw [l0 y z]

@[equational_result]
theorem Equation3419_implies_Equation41 (G : Type*) [Magma G] (h3419 : Equation3419 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3419 X0 X1 X0]
    conv => enter [1]; rw [← h3419 X3 X1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (X0 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3419 sK1 sK2 X0]
  have l2 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ X0) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [h3419 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [l0 X0 sK2 sK1]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3419 sK0 sK0 X0]
  have l5 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h3419 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 X0 sK0 sK0]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2 sK1]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK2 (sK1 ◇ sK2) X0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1]; rw [l5 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation3427 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3427 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l1 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ sK1) = (sK3 ◇ sK0) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y w z]
  conv => enter [1]; rw [l0 w z]

@[equational_result]
theorem Equation3427_implies_Equation41 (G : Type*) [Magma G] (h3427 : Equation3427 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h3427 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3427 X4 X5 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3413 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3413 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x z (z ◇ (x ◇ x))]

@[equational_result]
theorem Equation3413_implies_Equation41 (G : Type*) [Magma G] (h3413 : Equation3413 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h3413 sK0 sK0 sK0]
    conv => enter [1]; rw [← h3413 sK0 X1 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3413 X0 X1 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation3360 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3360 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation3360_implies_Equation41 (G : Type*) [Magma G] (h3360 : Equation3360 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3360 X0 X1 X0]
    conv => enter [1]; rw [← h3360 X3 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3360 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h3360 sK1 sK2 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3360 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation3428 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3428 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  intro x y z w
  conv => enter [1]; rw [← h41 w x y]
  conv => enter [1]; rw [l0 w z]

@[equational_result]
theorem Equation3428_implies_Equation41 (G : Type*) [Magma G] (h3428 : Equation3428 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h3428 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3428 X4 X5 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation3354 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3354 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y x z]

@[equational_result]
theorem Equation3354_implies_Equation41 (G : Type*) [Magma G] (h3354 : Equation3354 G) : Equation41 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h3354 X1 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3354 X0 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3354 X1 X0 X0]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3354 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l0 X0 X0]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l0 sK2 sK1]
    conv => enter [1]; rw [l0 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK1]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3354 sK1 sK2 sK2]
    conv => enter [1]; rw [← l4 sK2 sK1]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 (sK1 ◇ sK2)]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3354 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l3 X0 (sK1 ◇ sK2)]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← l3 X0 (sK1 ◇ sK2)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l9 X0 sK0]
  have l11 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l7 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 (sK1 ◇ sK2)]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 X0]
    conv => enter [1]; rw [← l11 sK1 X0 sK2]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation3416 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3416 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [← l0 z x w y]

@[equational_result]
theorem Equation3416_implies_Equation41 (G : Type*) [Magma G] (h3416 : Equation3416 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h3416 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3416 X0 X4 X0 X0]
  have l1 : ∀ sK1 sK2 X0 X2 : G, (sK1 ◇ sK2) = (X0 ◇ X2) := by
    intro sK1 sK2 X0 X2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [← h3416 X0 X2 sK1 sK1]
  have l2 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h3416 X0 X2 sK0 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3358 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3358 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 z x y]
  conv => enter [1]; rw [l0 z x y]

theorem Equation3358_4512_implies_Equation41 (G : Type*) [Magma G] (h3358 : Equation3358 G) (h4512 : Equation4512 G) : Equation41 G := by
  have l0 : ∀ X1 X3 X0 X2 : G, ((X1 ◇ (X3 ◇ X0)) ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X3 X0 X2
    conv => enter [1]; rw [h3358 (X1 ◇ (X3 ◇ X0)) X2 X1]
    conv => enter [1, 2, 2]; rw [← h3358 X0 X1 X3]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = ((X1 ◇ (X3 ◇ X0)) ◇ X2) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h3358 X1 X2 X0]
    conv => enter [1]; rw [← l0 X1 X3 X0 X2]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X1 ◇ ((X3 ◇ X0) ◇ X2)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X1 (X3 ◇ X0) X2]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X1 ◇ (X3 ◇ (X0 ◇ X2))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X3 X0 X2]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3358 (sK1 ◇ sK2) X0 X0]
    conv => enter [1, 2]; rw [← h3358 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ X0))) = ((sK2 ◇ (X1 ◇ X0)) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 (sK2 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h3358 X0 sK2 X1]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h3358 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK2) (sK2 ◇ sK2)]
  have l8 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ X0))) = (sK2 ◇ ((X1 ◇ X0) ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l5 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← h4512 sK2 (X1 ◇ X0) (X0 ◇ sK2)]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK2 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l7 sK1 sK2]
  have l10 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (X1 ◇ X0))) = (sK2 ◇ sK2) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l8 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← l3 sK2 sK2 (X1 ◇ X0) X0]
  have l11 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [← l4 sK1 sK2 (sK1 ◇ sK2)]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 (sK1 ◇ sK2) X0 sK2 sK1]
    conv => enter [1]; rw [l10 sK1 sK2 sK1 X0]
  have l13 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h3358 sK2 X0 sK2]
    conv => enter [1, 2, 2]; rw [l11 sK2 sK1]
  have l14 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l13 sK2 X0 sK1]
    conv => enter [1]; rw [← h3358 (sK1 ◇ sK2) X0 (sK1 ◇ sK2)]
  have l15 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l12 sK1 sK2 X0]
    conv => enter [1]; rw [← l12 sK1 sK2 X1]
  have l16 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h3358 X1 X0 (X1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l12 X1 sK2 X1]
  have l17 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) = (sK2 ◇ X1) := by
    intro X1 sK1 sK2 X0
    conv => enter [1, 2, 2]; rw [l12 sK1 sK2 X0]
    conv => enter [1]; rw [← h3358 sK2 X1 sK2]
  have l18 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l14 sK2 X1 sK1]
    conv => enter [1]; rw [← l17 X1 sK1 sK2 X0]
  have l19 : ∀ sK2 X0 X1 : G, (sK2 ◇ X0) = (X1 ◇ X0) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h3358 sK2 X0 sK2]
    conv => enter [1]; rw [← l16 X1 X0 sK2]
  have l20 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h3358 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l18 sK1 sK2 X1 X0]
  have l21 : ∀ X1 sK1 sK2 X0 X2 : G, (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) = (X2 ◇ X1) := by
    intro X1 sK1 sK2 X0 X2
    conv => enter [1, 2, 2]; rw [l15 sK1 sK2 X0 X2]
    conv => enter [1]; rw [← h3358 X2 X1 (sK1 ◇ sK2)]
  have l22 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l15 sK1 sK2 X0 ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h3358 sK0 (sK1 ◇ sK2) sK0]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3358 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l21 X1 X0 X0 X0 X2]
  have l24 : ∀ X2 X0 sK2 X1 : G, (X2 ◇ X0) = (sK2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 sK2 X1
    conv => enter [1]; rw [h3358 X2 X0 X1]
    conv => enter [1]; rw [l19 X0 (X0 ◇ (X1 ◇ X2)) sK2]
  have l25 : ∀ X2 X0 sK2 : G, (X2 ◇ X0) = (sK2 ◇ X2) := by
    intro X2 X0 sK2
    conv => enter [1]; rw [l24 X2 X0 sK2 X2]
    conv => enter [1]; rw [← l3 sK2 X2 X0 X2]
  have l26 : ∀ X2 X0 sK1 sK2 : G, (X2 ◇ X0) = ((sK1 ◇ sK2) ◇ X2) := by
    intro X2 X0 sK1 sK2
    conv => enter [1]; rw [l25 X2 X0 sK2]
    conv => enter [1]; rw [l20 sK2 X2 sK1 sK2]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [l26 (sK1 ◇ sK2) sK2 sK1 sK2]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [l22 sK1 sK2 (sK1 ◇ sK2) sK0]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l28 sK1 sK2 sK1]
    conv => enter [1]; rw [l23 sK1 (sK1 ◇ sK2) X0]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l22 sK1 sK2 sK0 sK0]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l29 sK1 sK2 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l31 y z x]

@[equational_result]
theorem Equation41_implies_Equation3425 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3425 G := by
  have l0 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 w x y]
  conv => enter [1]; rw [l0 w x z]

@[equational_result]
theorem Equation3425_implies_Equation41 (G : Type*) [Magma G] (h3425 : Equation3425 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h3425 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3425 X0 X4 X0 X0]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [h3425 X1 X2 sK1 X1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (X1 ◇ X1)) sK2]
  have l2 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [h3425 X1 X2 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ X1)) sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l3 y z x]

@[equational_result]
theorem Equation41_implies_Equation3361 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3361 G := by
  have l0 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  have l1 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ sK1) = (sK2 ◇ sK3) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w y]

@[equational_result]
theorem Equation3361_implies_Equation41 (G : Type*) [Magma G] (h3361 : Equation3361 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h3361 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3361 X4 X1 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3361 sK0 sK0 sK1 sK2]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3361 sK1 sK2 sK1 sK2]
  have l3 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3361 X0 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l2 sK1 sK2]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ sK2) X0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

@[equational_result]
theorem Equation41_implies_Equation3420 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3420 G := by
  have l0 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK2) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [← l1 y w x]
  conv => enter [1]; rw [l0 y w z]

@[equational_result]
theorem Equation3420_implies_Equation41 (G : Type*) [Magma G] (h3420 : Equation3420 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h3420 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3420 X4 X1 X0 X0]
  have l1 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ sK0) = (X2 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [h3420 X0 sK0 X1 sK0]
    conv => enter [1]; rw [l0 X1 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l2 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l1 sK0 sK0 X2 X1]
  have l3 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ X1) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 2]; rw [l2 sK0 X0 X1]
    conv => enter [1]; rw [← h3420 X2 X1 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 X0 sK0 sK0 sK0]
  have l5 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← l3 X0 sK0 sK1 sK2]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation41_implies_Equation3429 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation3429 G := by
  have l0 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK2 (sK2 ◇ (sK3 ◇ sK4))]
  have l1 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ sK4) = (sK1 ◇ sK0) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l1 x y w u]
  conv => enter [1]; rw [l0 w u z]

@[equational_result]
theorem Equation3429_implies_Equation41 (G : Type*) [Magma G] (h3429 : Equation3429 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h3429 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3429 X5 X6 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation41885 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41885 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_41885_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41885 : Equation41885 G) : Equation41 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h41885 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41885 X0 X0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41885 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h41885 X0 (sK0 ◇ sK0) X1]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41885 X0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0 X0]
  have l5 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X2]
    conv => enter [1, 2]; rw [← h41885 X0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l8 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l6 X1 X0]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h41885 X0 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← l5 X0 X1 X2]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l8 X0 X1 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [← l0 X0 X0]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l12 X0 X1]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l13 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1]; rw [← l14 X0 ((X0 ◇ X1) ◇ X2)]
  have l17 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l16 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l18 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l17 X0 X2 X1]
    conv => enter [1]; rw [← l14 X0 (X1 ◇ X2)]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 X0]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l21 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ X0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l18 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l20 sK0 X0 X1]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ sK0) X0]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l21 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 X1]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l22 sK0 X0]
  have l25 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l23 X0 X1 sK0]
    conv => enter [1]; rw [← l18 sK0 X1 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [l25 (sK0 ◇ sK0) X0 sK0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41885 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l27 sK0 X0]
  have l29 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l28 X0 X1 sK0]
    conv => enter [1]; rw [← l11 X0 X1 (sK0 ◇ sK0)]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l29 X0 X1 sK0]
    conv => enter [1]; rw [← l18 X0 (sK0 ◇ sK0) X1]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l30 X0 X1 sK0]
    conv => enter [1]; rw [← l27 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l31 y z x]

@[equational_result]
theorem Equation41_implies_Equation41888 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41888 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_41888_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41888 : Equation41888 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41888 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41888 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41888 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l8 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l9 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)))]
    conv => enter [1]; rw [← h41888 X0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41888 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0 X1]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l12 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l11 sK0 X0]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l13 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l11 sK0 X0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l14 X0 X1 sK0]
    conv => enter [1]; rw [← l11 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l15 y z x]

@[equational_result]
theorem Equation41_implies_Equation41889 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41889 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK0]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 z x y]

end Semigroup5
