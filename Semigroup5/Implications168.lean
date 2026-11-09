import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation41_implies_Equation42404 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42404 G := by
  have l0 : ∀ sK3 sK4 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK2 (sK0 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK3 sK4 sK1 : G, (sK3 ◇ sK4) = (sK1 ◇ sK1) := by
    intro sK3 sK4 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK1 sK1]
  have l2 : ∀ sK1 sK5 sK2 sK0 : G, (sK1 ◇ sK1) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK5 sK2 sK0
    conv => enter [1]; rw [h41 sK1 sK5 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK2 sK0 sK1]
  have l3 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK3 sK4 sK1]
    conv => enter [1]; rw [l2 sK1 sK5 sK2 sK0]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y z w u v]

@[equational_result]
theorem Equation42404_implies_Equation41 (G : Type*) [Magma G] (h42404 : Equation42404 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42404 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42404 X2 X3 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42405 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42405 G := by
  have l0 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK4 sK4 sK5]
    conv => enter [1]; rw [h41 sK4 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  intro x y z w u v r
  conv => enter [1]; rw [l0 x y z w u v r]

@[equational_result]
theorem Equation42405_implies_Equation41 (G : Type*) [Magma G] (h42405 : Equation42405 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42405 X0 X1 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42405 X2 X3 X0 X0 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42232 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42232 G := by
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [h41 z z (z ◇ (z ◇ (z ◇ z)))]

@[equational_result]
theorem Equation42232_implies_Equation41 (G : Type*) [Magma G] (h42232 : Equation42232 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h42232 X0 X1 X0]
    conv => enter [1]; rw [← h42232 X3 X4 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42230 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42230 G := by
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
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation42230_implies_Equation41 (G : Type*) [Magma G] (h42230 : Equation42230 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42230 X0 X1 X0]
    conv => enter [1]; rw [← h42230 X0 X3 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42230 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41935 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41935 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation4512_41935_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41935 : Equation41935 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41935 X0 X1 X0]
    conv => enter [1]; rw [← h41935 X3 X1 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l0 sK0 X1]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK0 ◇ X1) X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41935 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ X0))]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X0)]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (sK0 ◇ X0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l3 sK0 X0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) X0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42233 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42233 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l0 z w x y]

@[equational_result]
theorem Equation42233_implies_Equation41 (G : Type*) [Magma G] (h42233 : Equation42233 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42224 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42224 G := by
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
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation42224_implies_Equation41 (G : Type*) [Magma G] (h42224 : Equation42224 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42224 X0 X1 X0]
    conv => enter [1]; rw [← h42224 X0 X3 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42224 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42228 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42228 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK0]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK0]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]
  conv => enter [1]; rw [l0 y z]

theorem Equation4512_42228_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42228 : Equation42228 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42228 X0 X1 X0]
    conv => enter [1]; rw [← h42228 X3 X1 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42228 X1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l1 X0 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
  have l6 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l3 X1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l6 X1 X0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l7 X1 X0 sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l9 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l8 X1 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42236 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42236 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l1 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ sK1) = (sK3 ◇ sK0) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y w z]
  conv => enter [1]; rw [l0 w z]

@[equational_result]
theorem Equation42236_implies_Equation41 (G : Type*) [Magma G] (h42236 : Equation42236 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42236 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42236 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42222 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42222 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x z (z ◇ (z ◇ (x ◇ x)))]

@[equational_result]
theorem Equation42222_implies_Equation41 (G : Type*) [Magma G] (h42222 : Equation42222 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42222 sK0 sK0 sK0]
    conv => enter [1]; rw [← h42222 sK0 X1 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42222 X0 X1 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation41938 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41938 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l0 z y]

theorem Equation4512_41938_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41938 : Equation41938 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41938 X0 X1 X0]
    conv => enter [1]; rw [← h41938 X3 X1 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41938 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (X0 ◇ X0))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (X0 ◇ X0)]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42237 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42237 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  intro x y z w
  conv => enter [1]; rw [← h41 w x y]
  conv => enter [1]; rw [l0 w z]

@[equational_result]
theorem Equation42237_implies_Equation41 (G : Type*) [Magma G] (h42237 : Equation42237 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation41932 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41932 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y x z]

theorem Equation4512_41932_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41932 : Equation41932 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [h41932 sK1 X1 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41932 (sK0 ◇ sK0) X1 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41932 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h41932 sK0 X1 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 X1 sK0]
  have l6 : ∀ sK1 X1 sK2 : G, (sK1 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 X1 sK2
    conv => enter [1]; rw [l1 sK1 X1 sK2 sK1]
    conv => enter [1]; rw [← h41932 (sK1 ◇ sK2) X1 sK1]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [← l5 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h41932 X0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))]
    conv => enter [1]; rw [← h41932 X0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41932 X1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK0 X1]
  have l13 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l12 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l11 sK0 X0]
  have l14 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l13 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l11 sK0 X0]
  have l15 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l14 X1 X0 sK0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK2]
    conv => enter [1]; rw [l15 (sK1 ◇ sK2) sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l16 y z x]

@[equational_result]
theorem Equation41_implies_Equation42225 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42225 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [← l0 z x w y]

@[equational_result]
theorem Equation42225_implies_Equation41 (G : Type*) [Magma G] (h42225 : Equation42225 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  have l1 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ sK0)))]
    conv => enter [1]; rw [← h42225 X0 X2 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41936 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41936 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 z x y]
  conv => enter [1]; rw [l0 z x y]

theorem Equation4512_41936_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41936 : Equation41936 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41936 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41936 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = (X1 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h41936 X1 sK0 X0]
  have l4 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← h41936 X0 X1 X2]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l4 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h41936 (sK0 ◇ sK0) X0 sK0]
  have l8 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l5 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ X0)) X3]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l10 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ X0) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
  have l12 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X3)) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l10 X0 X1 X3 X0]
    conv => enter [1]; rw [← h41936 X3 X1 (X0 ◇ X0)]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l12 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l13 X0 sK0]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41936 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l7 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0)))]
  have l16 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ (X1 ◇ X0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l15 X0 sK0 X1]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (X1 ◇ X0))]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((X1 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l16 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X1 ◇ X0) (sK0 ◇ sK0)]
  have l18 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l17 X0 sK0 X1]
    conv => enter [1]; rw [l12 (sK0 ◇ sK0) (X1 ◇ X0) (sK0 ◇ sK0)]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l12 (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [← l18 X0 sK0 X1]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK0]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l21 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK0]
    conv => enter [1]; rw [l19 sK0 sK1 sK0]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← l21 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l22 x y z]

@[equational_result]
theorem Equation41_implies_Equation42234 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42234 G := by
  have l0 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 w x y]
  conv => enter [1]; rw [l0 w x z]

@[equational_result]
theorem Equation42234_implies_Equation41 (G : Type*) [Magma G] (h42234 : Equation42234 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42234 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42234 X0 X4 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [h42234 X1 X2 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (X1 ◇ X1))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41939 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41939 G := by
  have l0 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l1 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ sK1) = (sK2 ◇ sK3) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_41939_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41939 : Equation41939 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41939 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41939 X4 X1 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41939 sK0 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) (X0 ◇ X1)]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK1 sK2]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l9 sK1 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation42229 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42229 G := by
  have l0 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK2) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [← l1 y w x]
  conv => enter [1]; rw [l0 y w z]

theorem Equation4512_42229_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42229 : Equation42229 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X1 X4 : G, (X2 ◇ (X0 ◇ X1)) = (X4 ◇ X2) := by
    intro X2 X0 X1 X4
    conv => enter [1, 2]; rw [h42229 X0 X1 X2 X2]
    conv => enter [1]; rw [← h42229 X4 X2 X2 (X1 ◇ X2)]
  have l1 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42229 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42229 X4 X1 X0 X0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0 sK1]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ sK0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 sK0 X1 X0]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← l4 sK0 X1 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation41_implies_Equation42238 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42238 G := by
  have l0 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
  have l1 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ sK4) = (sK1 ◇ sK0) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l1 x y w u]
  conv => enter [1]; rw [l0 w u z]

@[equational_result]
theorem Equation42238_implies_Equation41 (G : Type*) [Magma G] (h42238 : Equation42238 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42198 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42198 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l2 z x]

@[equational_result]
theorem Equation42198_implies_Equation41 (G : Type*) [Magma G] (h42198 : Equation42198 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42198 X0 X1 X0]
    conv => enter [1]; rw [← h42198 X0 X3 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42198 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42198 X0 X1 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation41_implies_Equation42215 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42215 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l5 z y]

theorem Equation4512_42215_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42215 : Equation42215 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42215 X0 X1 X0]
    conv => enter [1]; rw [← h42215 X3 X1 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X1]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ X1) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ X0) = (sK2 ◇ (sK2 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [h42215 X1 X0 sK2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK2 sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l4 X1 X0 sK2 sK1]
    conv => enter [1]; rw [← l1 sK1 sK2 (X0 ◇ (sK1 ◇ sK2)) sK2]
  have l8 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l7 X1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 X0]
  have l9 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ X0) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l6 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l8 X1 X0 sK1 sK2]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation41_implies_Equation42251 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42251 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1]
    conv => enter [1, 2]; rw [← l1 sK2 sK1]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41 sK1 sK1 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l2 sK2 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK1 sK2]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l4 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l5 z w]

@[equational_result]
theorem Equation42251_implies_Equation41 (G : Type*) [Magma G] (h42251 : Equation42251 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42251 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42251 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42196 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42196 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation42196_implies_Equation41 (G : Type*) [Magma G] (h42196 : Equation42196 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42196 X0 X1 X0]
    conv => enter [1]; rw [← h42196 X0 X3 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42196 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41946 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41946 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]
  conv => enter [1]; rw [l3 y z]

theorem Equation4512_41946_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41946 : Equation41946 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41946 X0 X1 X0]
    conv => enter [1]; rw [← h41946 X3 X1 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41946 X1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l0 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l2 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l5 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l6 X1 X0 sK0]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42252 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42252 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK1 ◇ sK2)]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l3 z w]

@[equational_result]
theorem Equation42252_implies_Equation41 (G : Type*) [Magma G] (h42252 : Equation42252 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42252 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42252 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation41925 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41925 G := by
  have l0 : ∀ X1 X2 sK0 sK2 : G, (X1 ◇ X2) = (sK0 ◇ sK2) := by
    intro X1 X2 sK0 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK2]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK2]
    conv => enter [1]; rw [h41 sK0 sK1 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK1]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK1]
  have l4 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK2]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]
  conv => enter [1]; rw [l3 y z x]

theorem Equation4512_41925_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41925 : Equation41925 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41925 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
    conv => enter [1]; rw [← h41925 X0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41925 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 X0]
  have l4 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l3 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 X1]
  have l5 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l4 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 X0]
  have l6 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l5 X1 X0 sK0]
    conv => enter [1]; rw [← l2 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation41_implies_Equation42199 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42199 G := by
  have l0 : ∀ X1 X2 sK1 sK3 : G, (X1 ◇ X2) = (sK1 ◇ sK3) := by
    intro X1 X2 sK1 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK3]
  have l1 : ∀ sK1 sK3 sK2 : G, (sK1 ◇ sK3) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK3]
    conv => enter [1]; rw [h41 sK1 sK2 (sK1 ◇ sK3)]
  have l2 : ∀ sK1 sK3 sK2 : G, (sK1 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK3 sK2
    conv => enter [1]; rw [l0 sK1 sK3 sK1 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK1 sK3 sK2]
  have l3 : ∀ sK1 sK3 sK2 : G, (sK1 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK3 sK2
    conv => enter [1]; rw [l0 sK1 sK3 sK1 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK1 sK3 sK2]
  have l4 : ∀ sK1 sK3 sK2 sK0 : G, (sK1 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK3]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l3 z w x]

@[equational_result]
theorem Equation42199_implies_Equation41 (G : Type*) [Magma G] (h42199 : Equation42199 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42199 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42199 X0 X4 X0 X0]
  have l1 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← h42199 X0 X2 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41944 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41944 G := by
  have l0 : ∀ X1 X2 sK0 sK2 : G, (X1 ◇ X2) = (sK0 ◇ sK2) := by
    intro X1 X2 sK0 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK2]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK2]
    conv => enter [1]; rw [h41 sK0 sK1 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK1]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK1]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK2]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [l3 y x z]

theorem Equation4512_41944_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41944 : Equation41944 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41944 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h41944 X0 sK0 sK0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41944 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1, 2]; rw [← l2 (sK0 ◇ sK0) sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h41944 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41944 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l12 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1, 2]; rw [← l12 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l17 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41944 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l16 sK0 (X0 ◇ X1)]
  have l18 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l17 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 X0]
  have l19 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l18 X1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

@[equational_result]
theorem Equation41_implies_Equation42249 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42249 G := by
  have l0 : ∀ X1 X2 sK1 sK3 : G, (X1 ◇ X2) = (sK1 ◇ sK3) := by
    intro X1 X2 sK1 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK3]
  have l1 : ∀ sK1 sK3 sK2 : G, (sK1 ◇ sK3) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK3]
    conv => enter [1]; rw [h41 sK1 sK2 (sK1 ◇ sK3)]
  have l2 : ∀ sK1 sK3 sK2 : G, (sK1 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK3 sK2
    conv => enter [1]; rw [l0 sK1 sK3 sK1 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK1 sK3 sK2]
  have l3 : ∀ sK1 sK3 sK2 : G, (sK1 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK3 sK2
    conv => enter [1]; rw [l0 sK1 sK3 sK1 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK1 sK3 sK2]
  have l4 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK3]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l4 z x y]
  conv => enter [1]; rw [l3 z x w]

@[equational_result]
theorem Equation42249_implies_Equation41 (G : Type*) [Magma G] (h42249 : Equation42249 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42249 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42249 X0 X4 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [h42249 X1 X2 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ (sK0 ◇ X1))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41947 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41947 G := by
  have l0 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK3)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ sK1) = (sK1 ◇ sK3) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK3]
  have l3 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z y w]

theorem Equation4512_41947_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41947 : Equation41947 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41947 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41947 X4 X1 X0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 (sK0 ◇ X1) sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41947 sK0 sK0 X0 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ X1))]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 X1]
    conv => enter [1, 2]; rw [l1 sK0 sK0 X1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42216 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42216 G := by
  have l0 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK3)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))]
  have l1 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK0 ◇ sK2) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK3)]
    conv => enter [1]; rw [h41 sK2 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [← l1 y z w x]
  conv => enter [1]; rw [l0 y z w]

theorem Equation4512_42216_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42216 : Equation42216 G) : Equation41 G := by
  have l0 : ∀ X3 X1 X0 : G, (X3 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X3 X1 X0
    conv => enter [1]; rw [h42216 X3 X1 X1 (X1 ◇ X3)]
    conv => enter [1, 2]; rw [← h42216 X0 X1 X1 X3]
  have l1 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42216 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42216 X4 X1 X0 X0]
  have l2 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42216 X1 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK2) sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← l0 X2 (sK0 ◇ sK0) X1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK1 ◇ sK2)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42253 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42253 G := by
  have l0 : ∀ sK3 sK2 sK4 : G, (sK3 ◇ (sK2 ◇ sK4)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK4)))) := by
    intro sK3 sK2 sK4
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ sK4)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK2 ◇ (sK3 ◇ (sK2 ◇ sK4)))]
  have l1 : ∀ sK3 sK2 sK4 sK1 sK0 : G, (sK3 ◇ (sK2 ◇ sK4)) = (sK1 ◇ sK0) := by
    intro sK3 sK2 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ sK4)]
    conv => enter [1]; rw [h41 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l1 w z u x y]
  conv => enter [1]; rw [l0 w z u]

@[equational_result]
theorem Equation42253_implies_Equation41 (G : Type*) [Magma G] (h42253 : Equation42253 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42253 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42253 X5 X6 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42190 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42190 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation42190_implies_Equation41 (G : Type*) [Magma G] (h42190 : Equation42190 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42190 X0 X1 X0]
    conv => enter [1]; rw [← h42190 X0 X3 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42190 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42211 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42211 G := by
  have l0 : ∀ X1 X2 sK1 sK0 : G, (X1 ◇ X2) = (sK1 ◇ sK0) := by
    intro X1 X2 sK1 sK0
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK0]
    conv => enter [1]; rw [h41 sK1 sK1 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK0]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]
  conv => enter [1]; rw [l3 y z]

theorem Equation4512_42211_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42211 : Equation42211 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42211 X0 X1 X0]
    conv => enter [1]; rw [← h42211 X3 X1 X0]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42211 X1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l0 X0 sK0 sK0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l1 X1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l4 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l6 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l5 X1 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42256 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42256 G := by
  have l0 : ∀ X1 X2 sK2 sK1 : G, (X1 ◇ X2) = (sK2 ◇ sK1) := by
    intro X1 X2 sK2 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK1]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ sK1)]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK2 sK1]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK2 sK1]
  have l4 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ sK1) = (sK3 ◇ sK0) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y w z]
  conv => enter [1]; rw [l3 w z]

@[equational_result]
theorem Equation42256_implies_Equation41 (G : Type*) [Magma G] (h42256 : Equation42256 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42256 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42256 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42188 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42188 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x z (z ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation42188_implies_Equation41 (G : Type*) [Magma G] (h42188 : Equation42188 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42188 sK0 sK0 sK0]
    conv => enter [1]; rw [← h42188 sK0 X1 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42188 X0 X1 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation41950 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41950 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l5 z y]

theorem Equation4512_41950_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41950 : Equation41950 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41950 X0 X1 X0]
    conv => enter [1]; rw [← h41950 X3 X1 X0]
  have l1 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (sK2 ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l0 X0 (sK2 ◇ X1) sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [h41950 X1 X0 sK2]
    conv => enter [1, 2, 2, 2]; rw [l0 sK2 sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l4 X1 X0 sK2 sK1]
    conv => enter [1, 2]; rw [l1 X0 sK2 (sK1 ◇ sK2) sK1]
  have l8 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l7 X1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 (sK1 ◇ sK2)]
  have l9 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ X0) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← l8 X1 X0 sK1 sK2]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42257 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42257 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK2 ◇ sK2))]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1]
    conv => enter [1, 2]; rw [← l1 sK2 sK1]
  have l3 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l2 sK2 sK2]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK2]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l4 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [← h41 w x y]
  conv => enter [1]; rw [l5 w z]

@[equational_result]
theorem Equation42257_implies_Equation41 (G : Type*) [Magma G] (h42257 : Equation42257 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42257 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42257 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation41922 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41922 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y x z]

theorem Equation4512_41922_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41922 : Equation41922 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41922 X1 X2 (X1 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2, 2]; rw [← h41922 X0 X1 X1]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h41922 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41922 sK0 X1 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41922 X1 X2 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41922 X0 X1 X1]
  have l5 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h41922 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X1))))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2]; rw [← h41922 X0 sK0 X1]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l6 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ (X0 ◇ X1))]
  have l8 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l5 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 ((sK0 ◇ sK0) ◇ X0) X1 sK0]
    conv => enter [1]; rw [← l3 sK0 X1 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41922 sK0 X0 sK0]
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) X0 sK0]
  have l11 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l4 (X0 ◇ (X1 ◇ X2)) X3 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X0 X1 X3 X2]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = ((X0 ◇ X1) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X0]
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X2 X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((X0 ◇ (X0 ◇ X1)) ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [← l4 (X0 ◇ (X0 ◇ X1)) sK0 (sK0 ◇ sK0)]
  have l14 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
    conv => enter [1]; rw [← l4 (X1 ◇ (X0 ◇ (X1 ◇ X2))) X3 X0]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l16 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ ((X0 ◇ X1) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) sK0]
  have l18 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l14 X0 X1 X3 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X2)) X3]
  have l19 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l15 sK0 X0 X1]
  have l20 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l17 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l22 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l18 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l23 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
    conv => enter [1]; rw [← l21 sK0 X0 sK0]
  have l25 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l22 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X3]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ sK0)]
  have l27 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l25 X0 X1 X3 X2]
    conv => enter [1]; rw [l23 X1 X0 X1 (X2 ◇ X3)]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l19 sK0 X0 sK0]
    conv => enter [1]; rw [← l26 sK0 X0]
  have l29 : ∀ X0 X1 X3 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l27 X0 X1 X3 X0]
    conv => enter [1]; rw [l23 X1 X0 X0 X3]
  have l30 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X1 ◇ (X0 ◇ X3)) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l12 X1 X3 X0]
    conv => enter [1]; rw [l29 X0 X1 X3]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ sK0)))]
    conv => enter [1]; rw [← h41922 X0 sK0 sK0]
  have l33 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l34 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l30 X0 X1 sK0]
    conv => enter [1]; rw [← l33 sK0 X1 X0]
  have l35 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l34 X0 X1 sK0]
    conv => enter [1]; rw [← l31 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l35 y z x]

@[equational_result]
theorem Equation41_implies_Equation42191 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42191 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [← l0 z x w y]

@[equational_result]
theorem Equation42191_implies_Equation41 (G : Type*) [Magma G] (h42191 : Equation42191 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42191 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42191 X0 X4 X0 X0]
  have l1 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ sK0)))]
    conv => enter [1]; rw [← h42191 X0 X2 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41948 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41948 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK1 ◇ sK2)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l4 z x y]
  conv => enter [1]; rw [l3 z x y]

theorem Equation4512_41948_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41948 : Equation41948 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41948 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41948 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41948 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ X0)]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41948 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 X0 sK0]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41948 (sK0 ◇ sK0) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l9 X0 sK0]
  have l11 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l9 X0 sK0]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l11 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l13 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l10 sK0 X1 sK0]
    conv => enter [1]; rw [← h41948 sK0 X1 sK0]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41948 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l13 sK0 X0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ X0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l14 X0 X1 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ X0) X1 sK0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l15 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 X1]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l2 X0 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [l18 sK0 X0]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41948 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l18 sK0 X0]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l22 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l18 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 sK0]
    conv => enter [1]; rw [l22 sK0 X0 X1]
  have l24 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l21 sK0 X0 X1]
  have l25 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l16 X0 sK0 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l16 X0 sK0 sK0]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 sK0]
    conv => enter [1]; rw [l24 sK0 X0 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1 X0]
    conv => enter [1, 2]; rw [← l23 X1 X0 X0]
  have l29 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l26 sK0 sK2]
  have l30 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l29 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 sK1 sK0 sK2]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
    conv => enter [1]; rw [← l30 sK1 sK2 sK0]
  have l32 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [l18 (sK1 ◇ sK2) sK0]
  have l33 : ∀ X1 X0 sK0 X2 : G, (X1 ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (X2 ◇ (X2 ◇ X0)))) := by
    intro X1 X0 sK0 X2
    conv => enter [1, 2]; rw [h41948 X0 sK0 X2]
    conv => enter [1, 2]; rw [← l27 sK0 (X2 ◇ (X2 ◇ X0)) sK0]
  have l34 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ sK0)) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l27 X1 (X2 ◇ (X2 ◇ X0)) sK0]
    conv => enter [1]; rw [← l33 X1 X0 sK0 X2]
  have l35 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l23 X1 X0 X1]
    conv => enter [1]; rw [← l34 X1 X2 X0 X1]
  have l36 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l35 X1 X0 X2]
    conv => enter [1, 2]; rw [← l28 X0 X2]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l13 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← l28 X0 (sK0 ◇ sK0)]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 X0]
    conv => enter [1]; rw [← l9 X0 sK0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l38 sK0 X0]
  have l40 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [l39 sK0 X0]
  have l41 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l40 sK0 X0]
    conv => enter [1]; rw [l18 X0 sK0]
  have l42 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [← l41 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l42 y z x]

@[equational_result]
theorem Equation41_implies_Equation42209 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42209 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK1 ◇ sK2)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [l3 y x z]

theorem Equation4512_42209_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42209 : Equation42209 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42209 X0 sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42209 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42209 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X1 ◇ (X1 ◇ X0))]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ (X1 ◇ X0)) sK0 sK0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l5 X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X1 ◇ ((X1 ◇ X0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X0) sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 sK0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [← h42209 X0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42209 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l11 X0 sK0]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l11 X0 sK0]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l13 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h42209 sK0 X0 sK0]
    conv => enter [1]; rw [← l12 sK0 X0 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42209 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l11 sK0 sK0]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2, 2]; rw [h42209 sK0 sK0 X1]
    conv => enter [1]; rw [← h42209 (sK0 ◇ (sK0 ◇ sK0)) X1 X0]
  have l18 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l17 X0 sK0 X1]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 sK0 X0]
  have l20 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l18 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l11 X0 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 (sK0 ◇ X0)]
  have l22 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l20 sK0 X1 X0]
    conv => enter [1]; rw [l14 sK0 sK0 X1]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 sK0]
    conv => enter [1]; rw [← l22 X0 sK0 sK0]
  have l24 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2, 2]; rw [l23 sK0 X1]
    conv => enter [1]; rw [← h42209 sK0 X1 X0]
  have l25 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (sK0 ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l11 X0 sK0]
    conv => enter [1]; rw [l24 X0 sK0 X1]
  have l26 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [l25 sK0 sK0 X1]
  have l27 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h42209 X1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l27 x y z]

@[equational_result]
theorem Equation41_implies_Equation42254 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42254 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ sK3)]
  have l2 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3]
  have l3 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK1 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1]
  have l4 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l4 w x y]
  conv => enter [1]; rw [l3 w x z]

@[equational_result]
theorem Equation42254_implies_Equation41 (G : Type*) [Magma G] (h42254 : Equation42254 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42254 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42254 X0 X4 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [h42254 X1 X2 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ (X1 ◇ X1))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41951 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41951 G := by
  have l0 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ sK1) = (sK2 ◇ sK3) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK3]
  have l3 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z w y]

theorem Equation4512_41951_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41951 : Equation41951 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41951 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41951 X4 X1 X0 X0]
  have l1 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ (sK2 ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l0 X0 (sK2 ◇ X1) sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41951 sK0 sK0 X0 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2 X0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK2 (sK2 ◇ X0) sK1]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) sK2 X0 sK1]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42212 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42212 G := by
  have l0 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK0 ◇ sK2) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h41 sK2 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [← l1 y w x]
  conv => enter [1]; rw [l0 y w z]

theorem Equation4512_42212_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42212 : Equation42212 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42212 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42212 X4 X1 X0 X0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X1) X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42212 sK0 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l2 sK0 (sK0 ◇ X1) X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 X1]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 sK0 X1]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ sK0) ◇ X1) sK0]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l8 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l7 sK1 sK2]
  have l9 : ∀ sK0 X2 X0 : G, (sK0 ◇ sK0) = (X2 ◇ X0) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l6 sK0 (X0 ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h42212 X2 X0 (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42258 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42258 G := by
  have l0 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ (sK3 ◇ sK4)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4)))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ sK4)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4)))]
  have l1 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ sK4)) = (sK1 ◇ sK0) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ sK4)]
    conv => enter [1]; rw [h41 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l1 w u x y]
  conv => enter [1]; rw [l0 w u z]

@[equational_result]
theorem Equation42258_implies_Equation41 (G : Type*) [Magma G] (h42258 : Equation42258 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42258 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42258 X5 X6 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation42202 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42202 G := by
  have l0 : ∀ sK3 sK1 sK2 sK0 : G, (sK3 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK3 sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 sK1]
    conv => enter [1]; rw [h41 sK3 sK2 sK0]
  have l1 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK1]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y w z]
  conv => enter [1]; rw [l1 w z x]

@[equational_result]
theorem Equation42202_implies_Equation41 (G : Type*) [Magma G] (h42202 : Equation42202 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42202 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42202 X0 X4 X0 X0]
  have l1 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← h42202 X0 X2 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42241 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42241 G := by
  have l0 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK1]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))]
  have l1 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ sK1) = (sK3 ◇ sK0) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 sK1]
    conv => enter [1]; rw [h41 sK3 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 x z w]

@[equational_result]
theorem Equation42241_implies_Equation41 (G : Type*) [Magma G] (h42241 : Equation42241 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42241 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42241 X0 X4 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [h42241 X1 X2 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ (X1 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42219 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42219 G := by
  have l0 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK1]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))]
  have l1 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK1]
    conv => enter [1]; rw [h41 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l1 x y w z]
  conv => enter [1]; rw [l0 w z y]

theorem Equation4512_42219_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42219 : Equation42219 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42219 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42219 X4 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42219 sK0 sK0 X0 X1]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l1 sK0 (X1 ◇ X0) X0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l7 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42219 X1 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l7 X1 X0 sK0]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42246 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42246 G := by
  have l0 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 sK1]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))]
  have l1 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ sK1) = (sK0 ◇ sK3) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 sK1]
    conv => enter [1]; rw [h41 sK3 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l1 y z x]
  conv => enter [1]; rw [l0 y z w]

theorem Equation4512_42246_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42246 : Equation42246 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42246 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42246 X4 X1 X0 X0]
  have l1 : ∀ sK0 X0 X2 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X2 ◇ X1) := by
    intro sK0 X0 X2 X1
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 sK0 X1]
    conv => enter [1]; rw [← h42246 X2 X1 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X2 ◇ X1) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l1 sK0 X0 X2 X1]
  have l5 : ∀ sK0 X2 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X2 ◇ X1) := by
    intro sK0 X2 X1
    conv => enter [1, 2]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X2 X1]
  have l6 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ X1) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X2 X1]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42261 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42261 G := by
  have l0 : ∀ sK4 sK2 sK3 : G, (sK4 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK2)))) := by
    intro sK4 sK2 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 sK2]
    conv => enter [1]; rw [h41 sK4 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK2)))]
  have l1 : ∀ sK4 sK2 sK1 sK0 : G, (sK4 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK4 sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK4 sK4 sK2]
    conv => enter [1]; rw [h41 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l1 x y u z]
  conv => enter [1]; rw [l0 u z w]

@[equational_result]
theorem Equation42261_implies_Equation41 (G : Type*) [Magma G] (h42261 : Equation42261 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42261 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42261 X5 X6 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation41926 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41926 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK1 sK0]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [← l0 z x y]
  conv => enter [1]; rw [l1 z x y]

theorem Equation4512_41926_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41926 : Equation41926 G) : Equation41 G := by
  have l0 : ∀ X1 X0 X3 X2 : G, ((X1 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X3 ◇ X0))) ◇ (X0 ◇ X1)))) := by
    intro X1 X0 X3 X2
    conv => enter [1]; rw [h41926 (X1 ◇ (X0 ◇ (X3 ◇ X0))) X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h41926 X0 X1 X3]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41926 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41926 (X0 ◇ (X1 ◇ X0)) X2 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h41926 X0 (X0 ◇ (X1 ◇ X0)) X1]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41926 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X0 ◇ (X2 ◇ X0))) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l6 : ∀ X1 X0 X3 X2 : G, ((X1 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) = (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ (X0 ◇ X1))))) := by
    intro X1 X0 X3 X2
    conv => enter [1]; rw [l0 X1 X0 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X3 ◇ X0)) (X0 ◇ X1)]
  have l7 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l5 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l9 : ∀ X1 X2 X0 X3 : G, (X1 ◇ X2) = ((X1 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X2) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l1 X1 X2 (X0 ◇ (X3 ◇ X0)) X0]
    conv => enter [1]; rw [← l6 X1 X0 X3 X2]
  have l10 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l7 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 X3]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X0 X1]
    conv => enter [1]; rw [l8 X2 X0 X1]
  have l12 : ∀ X1 X2 X0 X3 : G, (X1 ◇ X2) = (X1 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X2)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l9 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X3 ◇ X0)) X2]
  have l13 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l10 X0 X1 X3 X2]
  have l14 : ∀ X1 X2 X0 X3 : G, (X1 ◇ X2) = (X1 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X2))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l12 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X3 ◇ X0) X2]
  have l15 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l13 X0 X1 X3 X1]
    conv => enter [1, 2, 2]; rw [← l11 X0 X3 X1]
  have l16 : ∀ X1 X2 X0 X3 : G, (X1 ◇ X2) = (X1 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X2)))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l14 X1 X2 X0 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X3 X0 X2]
  have l17 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l16 X1 X2 X0 X1]
    conv => enter [1, 2]; rw [← l11 X0 X2 X1]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l19 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [← l17 sK1 X0 sK2]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2 sK1]
    conv => enter [1]; rw [← l19 sK1 sK2 (sK1 ◇ sK2)]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41926 (sK0 ◇ sK0) X1 X0]
    conv => enter [1, 2, 2]; rw [← l18 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l21 sK0 X1 X0]
    conv => enter [1]; rw [← l15 sK0 X1 (X0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l22 sK0 X1 X0]
    conv => enter [1]; rw [← l17 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l24 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1, 2]; rw [l17 sK0 sK0 sK0]
    conv => enter [1]; rw [← l23 sK0 X1 sK0]
  have l25 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l17 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 X1]
  have l26 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l17 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l25 sK0 X1]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0)))]
    conv => enter [1]; rw [← h41926 X0 (sK0 ◇ sK0) sK0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l26 X0 X1 sK0]
    conv => enter [1]; rw [← l27 sK0 X0]
  have l29 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2]
    conv => enter [1]; rw [l28 (sK1 ◇ sK2) (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l29 y z x]

@[equational_result]
theorem Equation41_implies_Equation42192 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42192 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l0 y x z]

theorem Equation4512_42192_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42192 : Equation42192 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h42192 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 sK1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h42192 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h42192 X0 X1 (X1 ◇ X0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42192 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42192 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ (X1 ◇ X0))]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ X1)]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42192 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h42192 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1, 2]; rw [h42192 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1, 2]; rw [l8 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1, 2]; rw [← l9 (sK0 ◇ sK0) X0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42192 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l14 sK0]
  have l19 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l20 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l19 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l21 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ sK2) ◇ sK1)]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1))]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK0]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1))]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l23 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 ((sK1 ◇ sK2) ◇ sK1)]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1))]
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l21 sK1 sK2 sK1]
    conv => enter [1]; rw [← l9 (sK1 ◇ sK2) sK1 sK1]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 ((sK1 ◇ sK2) ◇ sK1)]
    conv => enter [1]; rw [← l24 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 ((sK1 ◇ sK2) ◇ sK1)]
  have l29 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 (sK1 ◇ sK2) sK1 sK0]
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 ((sK1 ◇ sK2) ◇ sK1)]
    conv => enter [1]; rw [← l28 sK0 sK1 sK2]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [l29 sK1 sK2 sK0]
  have l32 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 (sK1 ◇ sK2) sK1 sK0]
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
  have l33 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
  have l34 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l26 sK1 sK2]
  have l35 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ sK0) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h42192 (sK1 ◇ sK2) sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← l31 sK1 sK2 sK0]
  have l36 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2, 2, 2]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [← h42192 (sK1 ◇ sK2) (sK0 ◇ sK0) X0]
  have l37 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l36 sK1 sK1 sK2 sK0]
  have l38 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l34 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h42192 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l39 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l34 sK1 sK2 sK1]
    conv => enter [1]; rw [l38 sK1 sK1 sK2]
  have l40 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l39 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l37 sK1 sK2 sK0]
  have l42 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h42192 (sK0 ◇ sK0) (sK1 ◇ sK2) X0]
    conv => enter [1, 2, 2, 2]; rw [← l37 sK1 sK2 sK0]
  have l43 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l20 sK0 ((sK1 ◇ sK2) ◇ sK0) sK0]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1]; rw [← l40 sK1 sK2 sK0]
  have l45 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 (sK1 ◇ sK2) sK0 sK0]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [← l45 sK0 sK1 sK2]
  have l47 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [← l46 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l47 y z x]

@[equational_result]
theorem Equation41_implies_Equation42200 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42200 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 sK2]
    conv => enter [1]; rw [h41 sK3 sK2 sK0]
  have l1 : ∀ sK3 sK2 sK1 : G, (sK3 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK2]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))]
  intro x y z w
  conv => enter [1]; rw [← l0 w x y]
  conv => enter [1]; rw [l1 w x z]

@[equational_result]
theorem Equation42200_implies_Equation41 (G : Type*) [Magma G] (h42200 : Equation42200 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42200 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42200 X0 X4 X0 X0]
  have l1 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ X0)))]
    conv => enter [1]; rw [← h42200 X0 X2 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41942 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41942 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 x z y]

theorem Equation4512_41942_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41942 : Equation41942 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41942 (X1 ◇ (X0 ◇ X1)) X2 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41942 X0 (X1 ◇ (X0 ◇ X1)) X1]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41942 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X2 ◇ (X0 ◇ X2))) X3]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41942 X0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X1 ◇ (X0 ◇ X1))]
  have l5 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X2)) X3]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1)))]
  have l8 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l5 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ X2) X3]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 sK0]
    conv => enter [1]; rw [← h41942 X0 (sK0 ◇ sK0) sK0]
  have l11 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l12 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l11 X0 X1 X3 X2]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (X1 ◇ ((X0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41942 (sK0 ◇ sK0) X1 (X0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l10 sK0 X0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l13 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l14 sK0 X1 sK0]
    conv => enter [1]; rw [← l12 sK0 X1 (sK0 ◇ sK0) sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41942 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l10 sK0 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41942 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41942 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l17 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l15 sK0 X0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l21 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l17 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l19 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1, 2]; rw [← l17 sK0 X0]
  have l25 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l26 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l25 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l27 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l26 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l17 sK0 X1]
  have l28 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l27 sK0 X0 X1]
  have l29 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l17 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l28 sK0 X0 X1]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l18 sK0 X0]
  have l31 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 1]; rw [← l18 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ sK0) X1]
  have l32 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l31 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l30 sK0 X0]
  have l34 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1]; rw [← l32 X0 sK0 X1]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 (X0 ◇ sK0)]
  have l36 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l34 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [l35 sK0 X0]
  have l38 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l36 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l17 sK0 X1]
  have l39 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l18 sK0 X0]
    conv => enter [1]; rw [l24 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l18 sK0 X0]
  have l40 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 X0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l41 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l37 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l42 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l41 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l43 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41942 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l40 sK0 X0]
  have l44 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l43 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [l38 (sK0 ◇ sK0) sK0 X0]
  have l45 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l44 X0 X1 sK0]
    conv => enter [1]; rw [← l22 ((sK0 ◇ sK0) ◇ X0) X1 sK0]
  have l46 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l45 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l47 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l46 X0 X1 sK0]
    conv => enter [1]; rw [← l17 sK0 (X0 ◇ X1)]
  have l48 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l39 X0 sK0]
  have l49 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (X1 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41942 sK0 X1 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l39 X0 sK0]
  have l50 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l49 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l51 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l50 sK0 X1 X0]
    conv => enter [1]; rw [l9 X1 X0 (sK0 ◇ sK0)]
  have l52 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l51 sK0 X1 X0]
    conv => enter [1]; rw [← l17 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ X1))]
  have l53 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l52 sK0 X1 X0]
    conv => enter [1]; rw [← l47 X0 ((sK0 ◇ sK0) ◇ X1) sK0]
  have l54 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l53 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l17 sK0 X1]
  have l55 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l48 sK0 sK2]
  have l56 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l55 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l17 sK0 sK2]
  have l57 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK0]
    conv => enter [1]; rw [l38 sK1 sK0 sK2]
  have l58 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l47 sK1 sK2 sK0]
    conv => enter [1]; rw [← l57 sK1 sK2 sK0]
  have l59 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l58 sK1 sK2 sK0]
    conv => enter [1]; rw [← l40 sK0 (sK1 ◇ sK2)]
  have l60 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((X0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l37 sK0 X0]
    conv => enter [1]; rw [l42 sK0 (X0 ◇ sK0)]
  have l61 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l60 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 (sK0 ◇ sK0)]
  have l62 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l61 sK0 X0]
    conv => enter [1]; rw [← l54 sK0 (sK0 ◇ sK0) X0]
  have l63 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l40 sK0 sK0]
    conv => enter [1]; rw [← l62 sK0 X0]
  have l64 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l63 sK0 X0]
    conv => enter [1]; rw [← l54 sK0 X0 sK0]
  have l65 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l59 sK1 sK2 sK0]
    conv => enter [1]; rw [← l64 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l65 y z x]

@[equational_result]
theorem Equation41_implies_Equation42242 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42242 G := by
  have l0 : ∀ sK3 sK2 sK1 : G, (sK3 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK2]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))]
  have l1 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 sK2]
    conv => enter [1]; rw [h41 sK3 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y w]
  conv => enter [1]; rw [l0 x w z]

@[equational_result]
theorem Equation42242_implies_Equation41 (G : Type*) [Magma G] (h42242 : Equation42242 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42242 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42242 X0 X4 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [h42242 X1 X2 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ (X1 ◇ X1))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41954 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41954 G := by
  have l0 : ∀ sK3 sK2 sK1 : G, (sK3 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK2]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))]
  have l1 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ sK1) = (sK3 ◇ sK2) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l1 x y w z]
  conv => enter [1]; rw [l0 w z y]

theorem Equation4512_41954_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41954 : Equation41954 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41954 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41954 X4 X1 X0 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0 sK1]
  have l6 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h41954 X1 X0 (sK1 ◇ sK2) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1 sK2]
  have l7 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l6 X1 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK2 (sK1 ◇ sK2)]
  have l8 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l7 X1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 X0]
  have l9 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ X0) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [← l8 X1 X0 sK1 sK2]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42247 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42247 G := by
  have l0 : ∀ sK3 sK2 sK1 : G, (sK3 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK2]
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))]
  have l1 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ sK2) = (sK0 ◇ sK3) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 sK2]
    conv => enter [1]; rw [h41 sK3 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l1 y w x]
  conv => enter [1]; rw [l0 y w z]

theorem Equation4512_42247_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42247 : Equation42247 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42247 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42247 X4 X1 X0 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ X2 X1 X0 sK0 : G, (X2 ◇ X1) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X1 X0 sK0
    conv => enter [1]; rw [h42247 X2 X1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X2 X1 X0 sK0 : G, (X2 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X2 X1 X0 sK0
    conv => enter [1]; rw [l2 X2 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ X2 X1 X0 sK0 : G, (X2 ◇ X1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X2 X1 X0 sK0
    conv => enter [1]; rw [l5 X2 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ X1) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l6 X2 X1 sK0 sK0]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42262 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42262 G := by
  have l0 : ∀ sK4 sK3 sK2 : G, (sK4 ◇ sK3) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK3)))) := by
    intro sK4 sK3 sK2
    conv => enter [1]; rw [← h41 sK4 sK4 sK3]
    conv => enter [1]; rw [h41 sK4 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK3)))]
  have l1 : ∀ sK4 sK3 sK1 sK0 : G, (sK4 ◇ sK3) = (sK1 ◇ sK0) := by
    intro sK4 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK4 sK4 sK3]
    conv => enter [1]; rw [h41 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l1 x y u w]
  conv => enter [1]; rw [l0 u w z]

@[equational_result]
theorem Equation42262_implies_Equation41 (G : Type*) [Magma G] (h42262 : Equation42262 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42262 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42262 X5 X6 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation41_implies_Equation41928 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41928 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41 sK2 sK1 sK0]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h41 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [← l0 z x y]
  conv => enter [1]; rw [l1 z y x]

theorem Equation4512_41928_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41928 : Equation41928 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41928 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41928 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X0)]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h41928 X0 sK0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1))))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1, 2]; rw [← h41928 X0 sK0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ (X1 ◇ X1))]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1)))]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ sK0) sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 sK0]
    conv => enter [1]; rw [← h41928 X0 (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l11 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41928 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2]; rw [l9 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41928 sK0 X0 sK0]
    conv => enter [1]; rw [← l18 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← l19 sK0 (X0 ◇ X0)]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X0]
  have l22 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [← h41928 X0 (sK0 ◇ sK0) X1]
  have l23 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l17 sK0 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l22 sK0 X0 X1]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← l3 sK0 X0 X0]
    conv => enter [1]; rw [l23 sK0 X0 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 (X0 ◇ X0)]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l26 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h41928 (X0 ◇ X0) sK0 X0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 sK0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 X0]
  have l30 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ sK0) X1]
  have l31 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l30 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l32 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l19 sK0 X1]
    conv => enter [1]; rw [l31 sK0 X1 X0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1, 2]; rw [← l19 sK0 X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 (sK0 ◇ X0)]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41928 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l34 sK0 sK0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 sK0 X0]
    conv => enter [1]; rw [← l35 sK0 X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0 X0]
  have l38 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41928 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l37 sK0 X0]
  have l39 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l38 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l25 X1 sK0]
  have l40 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l39 X0 X1 sK0]
    conv => enter [1]; rw [← l29 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l40 y z x]

@[equational_result]
theorem Equation41_implies_Equation42203 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42203 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [h41 sK3 sK2 sK0]
  have l1 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [← l0 w x y]
  conv => enter [1]; rw [l1 w z x]

@[equational_result]
theorem Equation42203_implies_Equation41 (G : Type*) [Magma G] (h42203 : Equation42203 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42203 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42203 X0 X4 X0 X0]
  have l1 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l0 sK0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← h42203 X0 X2 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation41940 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41940 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h41 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41940_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41940 : Equation41940 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41940 (X1 ◇ (X0 ◇ X0)) X2 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h41940 X0 (X1 ◇ (X0 ◇ X0)) X1]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41940 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h41940 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h41940 (X0 ◇ X0) X1 X1]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41940 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X0)]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X0 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← h41940 X0 X1 X2]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41940 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ (X0 ◇ X0))))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41940 X0 sK0 X1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l7 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 sK0 (X1 ◇ (X0 ◇ X0))]
  have l9 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l5 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X0))]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l12 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [← l2 X0 X2 X0 X1]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l8 sK0 X0 X0]
  have l14 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l9 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X0)) X3]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1, 2]; rw [← l6 X0 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l12 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l17 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l14 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l18 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l16 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l19 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l17 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 X3]
  have l20 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l19 X0 X1 X3 X0]
    conv => enter [1, 2, 2]; rw [← l18 X0 X3 X0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41940 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l13 sK0 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l26 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0 sK0]
    conv => enter [1]; rw [← l25 sK0]
  have l27 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41940 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK0 sK0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41940 sK0 X0 sK0]
    conv => enter [1]; rw [← l27 sK0 X0 sK0]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41940 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l28 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1]; rw [← l20 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l26 sK0]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [l31 sK0 X0 X1]
  have l33 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l15 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l34 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l15 X0 sK0]
  have l35 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l34 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l36 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l33 X0 X1 sK0]
  have l37 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l28 sK0 X1]
    conv => enter [1]; rw [← l35 sK0 X0 X1]
  have l38 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l32 sK0 X1 X0]
    conv => enter [1]; rw [l36 X0 X1 sK0]
  have l39 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l37 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l40 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l41 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ sK0) X1]
  have l42 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l41 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l43 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l40 sK0 X0 X1]
    conv => enter [1]; rw [← l38 sK0 X1 X0]
  have l44 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l42 sK0 X0 X1]
    conv => enter [1]; rw [← l39 X0 sK0 X1]
  have l45 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l44 sK0 X0 X1]
  have l46 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l43 sK0 X0 X1]
    conv => enter [1]; rw [l45 sK0 X0 X1]
  have l47 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l32 sK0 sK0 X0]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l46 sK0 sK0 sK0]
    conv => enter [1]; rw [← l47 sK0 X0 sK0]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0]
    conv => enter [1]; rw [← l28 sK0 X0]
  have l50 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41940 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l48 sK0 (X1 ◇ X1)]
  have l51 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ X0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l32 sK0 X0 X0]
    conv => enter [1]; rw [← l50 X1 X0 sK0]
  have l52 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1]; rw [l51 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l52 x y z]

@[equational_result]
theorem Equation41_implies_Equation42205 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42205 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h41 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l0 x z y]

theorem Equation4512_42205_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42205 : Equation42205 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h42205 (X1 ◇ (X0 ◇ X0)) (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 2, 2]; rw [← h42205 X0 X1 (X1 ◇ (X0 ◇ X0))]
  have l2 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h42205 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42205 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42205 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X0))]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) (X1 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l5 X0 sK0]
    conv => enter [1, 2]; rw [← l4 X0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h42205 X0 X1 X0]
    conv => enter [1]; rw [← l8 X2 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42205 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2, 2]; rw [← l7 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l14 sK0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2, 2]; rw [l10 sK0]
    conv => enter [1]; rw [← h42205 (sK0 ◇ sK0) X1 X0]
  have l17 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42205 sK0 X1 sK0]
    conv => enter [1]; rw [l16 sK0 X1 sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1, 2]; rw [← l17 sK0 X0]
  have l20 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42205 X1 X0 sK0]
    conv => enter [1, 2]; rw [l17 sK0 (X0 ◇ (X1 ◇ X1))]
  have l21 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ (X1 ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l20 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l4 X1 X0 sK0]
  have l22 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ X0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h42205 X1 X0 sK0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l21 X1 X1 X0]
    conv => enter [1]; rw [l22 X0 X0 X1]
  have l24 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42205 X0 sK0 X1]
    conv => enter [1, 2, 2]; rw [← l21 X0 X0 sK0]
  have l25 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1, 2]; rw [← l23 X1 X0]
    conv => enter [1]; rw [← l24 X0 sK0 X1]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h42205 X0 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [l23 X1 (X0 ◇ X0)]
  have l27 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h42205 (X0 ◇ X0) X2 X1]
    conv => enter [1, 2, 2, 2]; rw [l23 (X0 ◇ X0) X0]
  have l28 : ∀ X0 X2 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X2
    conv => enter [1]; rw [l27 X0 X2 X0]
    conv => enter [1]; rw [← l2 X0 X2 X0 X0]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l26 X0 X0]
    conv => enter [1]; rw [l25 X0 (X0 ◇ X0) sK0]
  have l30 : ∀ X0 X2 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X2 ◇ sK0) := by
    intro X0 X2 sK0
    conv => enter [1]; rw [l28 X0 X2]
    conv => enter [1]; rw [l25 X0 X2 sK0]
  have l31 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l29 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 X0 sK0]
  have l32 : ∀ X0 X2 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (X2 ◇ sK0) := by
    intro X0 X2 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l30 X0 X2 sK0]
  have l33 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← l23 X0 X0]
    conv => enter [1]; rw [l31 X0 sK0]
  have l34 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l33 X0 sK0]
    conv => enter [1]; rw [l32 X0 sK0 sK0]
  have l35 : ∀ X2 X1 X0 sK0 : G, (X2 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X1 X0 sK0
    conv => enter [1]; rw [h42205 X2 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l34 X2 sK0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [l23 (X0 ◇ X0) X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [l32 X0 X0 sK0]
  have l38 : ∀ X2 X1 sK0 : G, (X2 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X2 X1 sK0
    conv => enter [1]; rw [l35 X2 X1 X2 sK0]
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) X1 X2]
  have l39 : ∀ X2 X1 sK0 : G, (X2 ◇ X1) = (X1 ◇ sK0) := by
    intro X2 X1 sK0
    conv => enter [1]; rw [l38 X2 X1 sK0]
    conv => enter [1]; rw [l25 (sK0 ◇ sK0) X1 sK0]
  have l40 : ∀ X2 X1 sK0 : G, (X2 ◇ X1) = (sK0 ◇ sK0) := by
    intro X2 X1 sK0
    conv => enter [1]; rw [l39 X2 X1 sK0]
    conv => enter [1]; rw [← l37 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l40 y z x]

@[equational_result]
theorem Equation41_implies_Equation42239 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42239 G := by
  have l0 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l0 x z w]

theorem Equation4512_42239_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42239 : Equation42239 G) : Equation41 G := by
  have l0 : ∀ X4 X5 X2 X0 X1 : G, (X4 ◇ X5) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X4 X5 X2 X0 X1
    conv => enter [1]; rw [h42239 X4 X5 X2 X4]
    conv => enter [1, 2]; rw [h42239 X2 (X4 ◇ (X4 ◇ X4)) X0 X1]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42239 X0 X1 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42239 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (X0 ◇ X0)]
  have l3 : ∀ X4 X5 sK1 sK2 X2 : G, (X4 ◇ X5) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (X2 ◇ X2))) := by
    intro X4 X5 sK1 sK2 X2
    conv => enter [1]; rw [l0 X4 X5 X2 X4 X4]
    conv => enter [1]; rw [l2 X2 (X4 ◇ (X4 ◇ (X4 ◇ (X2 ◇ X2)))) sK1 sK2]
  have l4 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (sK0 ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [h42239 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h42239 sK0 X2 sK0 sK0]
  have l5 : ∀ X4 X5 sK0 sK1 : G, (X4 ◇ X5) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro X4 X5 sK0 sK1
    conv => enter [1]; rw [l3 X4 X5 sK1 X4 X4]
    conv => enter [1]; rw [l1 sK1 ((sK1 ◇ X4) ◇ (X4 ◇ X4)) sK0]
  have l6 : ∀ sK0 X4 X5 : G, (sK0 ◇ sK0) = (X4 ◇ X5) := by
    intro sK0 X4 X5
    conv => enter [1]; rw [l4 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l5 X4 X5 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation41_implies_Equation41955 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41955 G := by
  have l0 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [h41 sK3 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [← h41 w x y]
  conv => enter [1]; rw [l0 w y z]

end Semigroup5
