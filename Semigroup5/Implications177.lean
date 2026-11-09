import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41958_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41958 : Equation41958 G) : Equation343 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41958 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h41958 sK0 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41958 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [h41958 (sK0 ◇ sK1) ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h41958 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h41958 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((X0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [h41958 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ sK1)) X1]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK1) (X1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 sK0 (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l15 x y z]

@[equational_result]
theorem Equation343_implies_Equation41975 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation41975 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41975_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41975 : Equation41975 G) : Equation343 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [h41975 sK0 (sK1 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41975 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l2 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 X0 (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l1 (sK0 ◇ sK1) X0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41975 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h41975 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1]
  have l10 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h41975 X0 (sK0 ◇ sK1) X1]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [← l10 X0 sK0 sK1 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l7 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

@[equational_result]
theorem Equation343_implies_Equation41992 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation41992 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41992_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41992 : Equation41992 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = ((X2 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41992 X0 X1 X2]
    conv => enter [1]; rw [h41992 X1 (X2 ◇ (X2 ◇ (X0 ◇ X1))) X3]
    conv => enter [1, 2, 2, 2]; rw [← h41992 X0 X1 X2]
  have l1 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [h41992 sK0 (sK1 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 X0 (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X2 (X2 ◇ (X0 ◇ X1)) (X3 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h41992 (sK0 ◇ sK1) X0 sK0]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ X1) (X3 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← h41992 X0 X1 X0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41992 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h41992 sK0 sK1 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41992 sK0 sK1 sK1]
    conv => enter [1, 2, 2]; rw [l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 (sK0 ◇ sK1)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41992 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l12 sK2 sK0 sK1]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK1) = (((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [h41992 sK1 ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1)) (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [← l7 X0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l12 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

@[equational_result]
theorem Equation343_implies_Equation42009 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42009 G := by
  have l0 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [h343 sK0 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [h343 sK0 (sK1 ◇ sK2) sK3]
  intro x y z w
  conv => enter [1]; rw [h343 x y w]
  conv => enter [1]; rw [l0 w x y z]

theorem Equation4512_42009_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42009 : Equation42009 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h42009 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ X4) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [h42009 X3 X4 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X1 X1 X0]
    conv => enter [1]; rw [← l0 X0 X1 X2 X1 X1]
  have l3 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ sK1) = (sK1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h42009 sK0 sK1 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) sK1]
  have l5 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ sK1) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l4 sK0 sK1 sK0 X1 X2]
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (sK0 ◇ sK1)) sK0]
  have l6 : ∀ sK0 sK1 X2 : G, (sK0 ◇ sK1) = (X2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l5 sK0 sK1 sK0 X2]
    conv => enter [1]; rw [← l2 X2 (sK0 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation343_implies_Equation42035 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42035 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h343 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42035_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42035 : Equation42035 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42035 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42035 X0 X1 X0]
  have l2 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ sK1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h42035 sK0 sK1 X0]
    conv => enter [1]; rw [h42035 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
    conv => enter [1, 2, 2, 2]; rw [← h42035 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (sK0 ◇ sK1)) sK0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation343_implies_Equation42052 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42052 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h343 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42052_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42052 : Equation42052 G) : Equation343 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h42052 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42052 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42052 X0 X1 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l5 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l4 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) X0 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0]
  have l7 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l7 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation343_implies_Equation42069 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42069 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42069_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42069 : Equation42069 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h42069 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42069 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X3 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X0 ◇ (X1 ◇ X3)) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l2 X1 X3 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1 X3 X1]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ sK1) = (X1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h42069 sK0 sK1 X0]
    conv => enter [1]; rw [h42069 X0 (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) X1]
    conv => enter [1, 2, 2, 2]; rw [← h42069 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (sK0 ◇ sK1)) X1]
  have l7 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l6 sK0 sK1 sK0 X1]
    conv => enter [1]; rw [← l4 X1 (sK0 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation343_implies_Equation42086 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42086 G := by
  have l0 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [h343 sK0 (sK1 ◇ sK2) sK3]
    conv => enter [1, 2]; rw [h343 sK0 (sK1 ◇ sK2) sK1]
  intro x y z w
  conv => enter [1]; rw [h343 x y w]
  conv => enter [1]; rw [l0 w x y z]

theorem Equation4512_42086_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42086 : Equation42086 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X4 X2 X5 : G, (X0 ◇ X1) = (X4 ◇ (X2 ◇ (X5 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X4 X2 X5
    conv => enter [1]; rw [h42086 X0 X1 X2 X0]
    conv => enter [1]; rw [h42086 X2 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X4 X5]
    conv => enter [1, 2, 2, 2]; rw [← h42086 X0 X1 X2 X0]
  have l1 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ (X2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h42086 sK0 sK1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (X2 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ sK0 sK1 X2 : G, (sK0 ◇ sK1) = (X2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK0 X2]
    conv => enter [1]; rw [← l0 X2 (sK0 ◇ sK1) sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation343_implies_Equation42112 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42112 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h343 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42112_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42112 : Equation42112 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42112 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42112 X0 X1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42112 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h42112 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l6 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK1) sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation343_implies_Equation42129 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42129 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h343 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42129_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42129 : Equation42129 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42129 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42129 X0 X1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42129 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h42129 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l6 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation343_implies_Equation42146 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42146 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [h343 sK0 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h343 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42146_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42146 : Equation42146 G) : Equation343 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h42146 (X0 ◇ X1) (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h42146 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42146 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h42146 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h42146 sK1 (X0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← h42146 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42146 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l3 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42146 sK0 sK1 sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l8 sK1 sK0 (sK0 ◇ sK1)]
  have l12 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42146 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l12 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h42146 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK0 sK1]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) X0]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h42146 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l17 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l18 X0 sK0 sK1]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

@[equational_result]
theorem Equation343_implies_Equation42163 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42163 G := by
  have l0 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [h343 sK0 (sK1 ◇ sK2) sK3]
    conv => enter [1, 2]; rw [h343 sK0 (sK1 ◇ sK2) sK2]
  intro x y z w
  conv => enter [1]; rw [h343 x y w]
  conv => enter [1]; rw [l0 w x y z]

theorem Equation4512_42163_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42163 : Equation42163 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42163 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h42163 X2 (X0 ◇ X1) X0 X1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h42163 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation343_implies_Equation42266 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42266 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h343 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [h343 sK1 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [h343 w (x ◇ (x ◇ y)) z]

theorem Equation4512_42266_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42266 : Equation42266 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42266 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42266 X0 X1 X0 X0]
  have l2 : ∀ sK0 sK1 X2 X3 X0 : G, (sK0 ◇ sK1) = (X2 ◇ (X3 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X2 X3 X0
    conv => enter [1]; rw [h42266 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [h42266 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h42266 sK0 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 X3 X0 : G, (sK0 ◇ sK1) = (X3 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X3 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0 X3 X0]
    conv => enter [1]; rw [← l1 X3 (X0 ◇ (sK0 ◇ sK1)) sK0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [← l1 X0 (sK0 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation343_implies_Equation42292 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42292 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h343 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [h343 sK1 sK2 sK2]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [h343 w (y ◇ (x ◇ y)) z]

theorem Equation4512_42292_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42292 : Equation42292 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42292 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42292 X0 X1 X0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42292 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h42292 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l4 sK0 sK1 sK0 X1]
    conv => enter [1]; rw [← l1 X1 (sK0 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation343_implies_Equation42318 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42318 G := by
  have l0 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [h343 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [h343 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l0 x y w z]
  conv => enter [1]; rw [h343 w (z ◇ (x ◇ y)) z]

theorem Equation4512_42318_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42318 : Equation42318 G) : Equation343 G := by
  have l0 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ X4) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h42318 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42318 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X3 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l2 X0 X1 X0 X3 X0]
    conv => enter [1]; rw [← l0 X3 (X0 ◇ X1) X0 X3 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h42318 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation343_implies_Equation42344 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42344 G := by
  have l0 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [h343 sK0 (sK1 ◇ sK2) sK3]
    conv => enter [1, 2, 2]; rw [h343 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [h343 x y w]
  conv => enter [1]; rw [l0 w x y z]

theorem Equation4512_42344_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42344 : Equation42344 G) : Equation343 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 2]; rw [h42344 sK0 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h42344 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l0 sK2 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation343_implies_Equation42370 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42370 G := by
  have l0 : ∀ sK0 sK2 sK3 sK4 sK1 : G, (sK0 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK0 sK2 sK3 sK4 sK1
    conv => enter [1]; rw [h343 sK0 (sK2 ◇ sK3) sK4]
    conv => enter [1, 2]; rw [h343 sK0 (sK2 ◇ sK3) sK1]
  intro x y z w u
  conv => enter [1]; rw [h343 x y u]
  conv => enter [1]; rw [l0 u x y z w]

theorem Equation4512_42370_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42370 : Equation42370 G) : Equation343 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h42370 sK0 sK1 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h42370 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK0 sK0]
    conv => enter [1]; rw [← l0 sK2 sK0 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation343_implies_Equation42189 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42189 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h343 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [h343 sK1 sK2 sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h343 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42189_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42189 : Equation42189 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h42189 X0 X1 X2]
    conv => enter [1]; rw [h42189 X2 (X2 ◇ (X0 ◇ (X0 ◇ X1))) X3]
    conv => enter [1, 2, 2, 2]; rw [← h42189 X0 X1 X2]
  have l1 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ sK1) = (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h42189 sK0 sK1 X0]
    conv => enter [1]; rw [h42189 X0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
    conv => enter [1, 2, 2, 2]; rw [← h42189 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ sK1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0 X1]
    conv => enter [1]; rw [← l0 X1 (sK0 ◇ sK1) sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation343_implies_Equation41941 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation41941 G := by
  intro x y z
  conv => enter [1]; rw [h343 x y z]
  conv => enter [1]; rw [h343 z (x ◇ y) y]
  conv => enter [1, 2]; rw [h343 z (x ◇ y) y]

theorem Equation4512_41941_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41941 : Equation41941 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h41941 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41941 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X1 X0]
    conv => enter [1]; rw [← l0 X0 X1 X2 X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41941 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ (sK0 ◇ sK1)) sK1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (sK0 ◇ sK1)) sK1]
  have l6 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK0 X1]
    conv => enter [1]; rw [← l2 X1 (sK0 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation343_implies_Equation42206 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42206 G := by
  intro x y z
  conv => enter [1]; rw [h343 x y y]
  conv => enter [1]; rw [h343 y (x ◇ y) z]
  conv => enter [1, 2]; rw [h343 y (x ◇ y) z]

theorem Equation4512_42206_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42206 : Equation42206 G) : Equation343 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42206 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h42206 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← h42206 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h42206 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l4 sK2 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l9 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h42206 sK2 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h42206 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h42206 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0 sK1 sK2]
  have l12 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK2 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation343_implies_Equation42240 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation42240 G := by
  intro x y z w
  conv => enter [1]; rw [h343 x y w]
  conv => enter [1]; rw [h343 w (x ◇ y) z]
  conv => enter [1, 2]; rw [h343 w (x ◇ y) z]

theorem Equation4512_42240_implies_Equation343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42240 : Equation42240 G) : Equation343 G := by
  have l0 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ sK1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [h42240 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0 X1]
    conv => enter [1]; rw [← h42240 X1 (sK0 ◇ sK1) sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation3255_4512_implies_Equation41531 (G : Type*) [Magma G] (h3255 : Equation3255 G) (h4512 : Equation4512 G) : Equation41531 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3255 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h3255 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h3255 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h3255 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3255 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_41531_implies_Equation3255 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41531 : Equation41531 G) : Equation3255 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41531 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41531 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK1 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41531 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41531 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l11 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1, 2]; rw [← l13 sK0 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 (sK1 ◇ sK0)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation3255_4512_implies_Equation41537 (G : Type*) [Magma G] (h3255 : Equation3255 G) (h4512 : Equation4512 G) : Equation41537 G := by
  have l0 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [h3255 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l1 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l0 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l1 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3255 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [← h3255 (sK1 ◇ sK0) sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_41537_implies_Equation3255 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41537 : Equation41537 G) : Equation3255 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h41537 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41537 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41537 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41537 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ sK0)]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l5 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41537 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41537 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l13 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l15 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2]; rw [← l16 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l16 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l16 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2]; rw [← l17 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l17 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l23 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK1 ◇ sK0) ◇ sK0) X0]
  have l24 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l23 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l25 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l26 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [l25 sK1 sK0 X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l19 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1, 2]; rw [← l31 sK0 sK1]
  have l34 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41537 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l34 sK1 sK0]
  have l36 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l37 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l36 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l38 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l37 sK1 sK0 X0]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1, 2]; rw [← l26 sK1 sK0 (sK1 ◇ sK0)]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ sK0)]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 (sK1 ◇ sK0) (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l10 sK0 sK1]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1, 2]; rw [← l26 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← l38 sK1 sK0 sK0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41537 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l48 sK1 sK0]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ sK0)]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l52 x y]

theorem Equation3255_4512_implies_Equation41540 (G : Type*) [Magma G] (h3255 : Equation3255 G) (h4512 : Equation4512 G) : Equation41540 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h3255 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l0 sK0 X0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK2 ◇ sK0))]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4512_41540_implies_Equation3255 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41540 : Equation41540 G) : Equation3255 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41540 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l8 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 (sK1 ◇ sK0) sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation3258_4512_implies_Equation41544 (G : Type*) [Magma G] (h3258 : Equation3258 G) (h4512 : Equation4512 G) : Equation41544 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3258 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3258 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3258 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation4512_41544_implies_Equation3258 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41544 : Equation41544 G) : Equation3258 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41544 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41544 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41544 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l3 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3258_4512_implies_Equation41554 (G : Type*) [Magma G] (h3258 : Equation3258 G) (h4512 : Equation4512 G) : Equation41554 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3258 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3258 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_41554_implies_Equation3258 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41554 : Equation41554 G) : Equation3258 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41554 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41554 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l7 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41554 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1, 2]; rw [← l9 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l9 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41554 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l14 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41554 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2, 2]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l24 x y]

theorem Equation3258_4512_implies_Equation41564 (G : Type*) [Magma G] (h3258 : Equation3258 G) (h4512 : Equation4512 G) : Equation41564 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3258 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3258 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41564_implies_Equation3258 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41564 : Equation41564 G) : Equation3258 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41564 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41564 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (X0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41564 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3273_4512_implies_Equation3295 (G : Type*) [Magma G] (h3273 : Equation3273 G) (h4512 : Equation4512 G) : Equation3295 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h3273 (X1 ◇ X2) X0 X3]
    conv => enter [1]; rw [h3273 (X1 ◇ X2) X1 X2]
    conv => enter [1, 2]; rw [h3273 (X1 ◇ X2) X0 X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 (X0 ◇ X3)]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3273 X0 X1 (X2 ◇ (X0 ◇ X3))]
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
  have l3 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h3273 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [h3273 X0 sK1 sK1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0 X0 (X0 ◇ X0)]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK3]
    conv => enter [1]; rw [h3273 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation3295_implies_Equation3273 (G : Type*) [Magma G] (h3295 : Equation3295 G) : Equation3273 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h3295 X1 X1 X1 X1]
    conv => enter [1]; rw [← h3295 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3295 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation3301_implies_Equation3275 (G : Type*) [Magma G] (h3301 : Equation3301 G) : Equation3275 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h3301 X1 X1 X1 X1]
    conv => enter [1]; rw [← h3301 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3301 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation3275_implies_Equation3301 (G : Type*) [Magma G] (h3275 : Equation3275 G) : Equation3301 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3275 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h3275 X0 sK1 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h3275 (sK1 ◇ sK1) X0 X0]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h3275 X0 sK1 sK1]
    conv => enter [1, 2]; rw [l1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 sK1]
    conv => enter [1]; rw [← h3275 (sK1 ◇ sK1) sK1 sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK1]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK3]
    conv => enter [1]; rw [h3275 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation3301_implies_Equation3289 (G : Type*) [Magma G] (h3301 : Equation3301 G) : Equation3289 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h3301 X1 X1 X1 X1]
    conv => enter [1]; rw [← h3301 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3301 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation3289_4512_implies_Equation3301 (G : Type*) [Magma G] (h3289 : Equation3289 G) (h4512 : Equation4512 G) : Equation3301 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = ((X0 ◇ X2) ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h3289 X1 (X0 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h3289 X0 X2 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = (X0 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X2 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← h3289 X1 X1 X0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h3289 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation3304_implies_Equation3277 (G : Type*) [Magma G] (h3304 : Equation3304 G) : Equation3277 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h3304 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h3304 X0 X1 X1 X1 X1]
  have l1 : ∀ sK1 X1 sK3 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X1 sK3 sK0
    conv => enter [1]; rw [h3304 sK1 X1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

@[equational_result]
theorem Equation3277_implies_Equation3304 (G : Type*) [Magma G] (h3277 : Equation3277 G) : Equation3304 G := by
  have l0 : ∀ X0 sK4 sK1 sK0 X1 : G, (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK4 sK1 sK0 X1
    conv => enter [1]; rw [← h3277 sK4 X0 sK1 sK0]
    conv => enter [1]; rw [h3277 sK4 X1 sK1 sK0]
  have l1 : ∀ sK3 sK4 sK1 sK0 X0 : G, (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l0 sK3 sK4 sK1 sK0 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h3277 (sK4 ◇ (sK1 ◇ sK0)) X0 sK4 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK4 ◇ (sK1 ◇ sK0)) sK4 sK1 sK0 sK3]
  have l2 : ∀ X0 X1 sK4 sK1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK4 sK1 sK0 X2
    conv => enter [1]; rw [← h3277 X1 X0 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h3277 X1 X2 sK1 sK0]
  have l3 : ∀ X0 sK3 sK4 sK1 sK0 X2 X1 : G, (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK3 sK4 sK1 sK0 X2 X1
    conv => enter [1, 2]; rw [l0 sK3 sK4 sK1 sK0 X1]
    conv => enter [1]; rw [l2 X0 X1 sK4 sK1 sK0 X2]
  have l4 : ∀ sK3 sK4 sK1 sK0 X2 X1 : G, (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK4 sK1 sK0 X2 X1
    conv => enter [1]; rw [l1 sK3 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [l3 sK3 sK3 sK4 sK1 sK0 X2 X1]
  have l5 : ∀ sK3 sK4 sK1 sK0 X0 : G, (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (X0 ◇ X0) := by
    intro sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK4 sK1 sK0 sK3 X0]
    conv => enter [1]; rw [← h3277 X0 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l5 y z w u x]

@[equational_result]
theorem Equation3304_implies_Equation3291 (G : Type*) [Magma G] (h3304 : Equation3304 G) : Equation3291 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h3304 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h3304 X0 X1 X1 X1 X1]
  have l1 : ∀ sK1 X1 sK3 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 X1 sK3 sK0
    conv => enter [1]; rw [h3304 sK1 X1 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

@[equational_result]
theorem Equation3291_implies_Equation3304 (G : Type*) [Magma G] (h3291 : Equation3291 G) : Equation3304 G := by
  have l0 : ∀ X0 X1 X2 sK2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 X2 sK2
    conv => enter [1]; rw [h3291 X0 X1 X2 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← h3291 sK2 X0 X0 sK2]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [h3291 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← l0 X0 sK2 sK2 sK2]
  have l2 : ∀ sK2 X0 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1]
    conv => enter [1]; rw [h3291 sK1 X0 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

@[equational_result]
theorem Equation3290_implies_Equation3302 (G : Type*) [Magma G] (h3290 : Equation3290 G) : Equation3302 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3290 X1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3290 X0 (X0 ◇ X1) X1]
  have l1 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h3290 sK0 sK2 sK3]
    conv => enter [1]; rw [h3290 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [h3290 sK0 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK0 (sK0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))))]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) X0 X1]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h3290 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [l0 (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK1 sK1]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 sK1 sK1]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation3302_implies_Equation3290 (G : Type*) [Magma G] (h3302 : Equation3302 G) : Equation3290 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h3302 X1 X1 X1 X1]
    conv => enter [1]; rw [← h3302 X0 X1 X1 X1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3302 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation3316_4512_implies_Equation41770 (G : Type*) [Magma G] (h3316 : Equation3316 G) (h4512 : Equation4512 G) : Equation41770 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h3316 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ sK1)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation4512_41770_implies_Equation3316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41770 : Equation41770 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41770 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41770 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h41770 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK1)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation3316_4512_implies_Equation41780 (G : Type*) [Magma G] (h3316 : Equation3316 G) (h4512 : Equation4512 G) : Equation41780 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [h3316 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h3316 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h3316 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_41780_implies_Equation3316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41780 : Equation41780 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41780 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h41780 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3322_4512_implies_Equation41776 (G : Type*) [Magma G] (h3322 : Equation3322 G) (h4512 : Equation4512 G) : Equation41776 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3322 X0 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h3322 (sK2 ◇ sK1) sK1 sK2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3322 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l2 sK0 sK2 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK2 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_41776_implies_Equation3322 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41776 : Equation41776 G) : Equation3322 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK1) X0]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41776 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (X0 ◇ sK1))]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h41776 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ (X0 ◇ sK1))]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41776 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (X0 ◇ (sK2 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41776 sK0 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l10 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l4 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 sK1]
  have l11 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = ((sK2 ◇ sK1) ◇ (((sK2 ◇ sK1) ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ sK1) X0]
  have l12 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l11 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) sK1 X0]
  have l13 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41776 (sK2 ◇ sK1) sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) (sK0 ◇ sK1)]
  have l14 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h41776 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK0]
    conv => enter [1]; rw [l2 sK2 sK1 (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h41776 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l17 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l14 sK2 sK1 sK0]
    conv => enter [1]; rw [← l12 sK2 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
  have l19 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK1) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l13 sK2 sK1 sK2]
    conv => enter [1]; rw [← l17 sK2 sK1 sK2]
  have l20 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l19 sK2 sK1]
    conv => enter [1]; rw [l2 sK2 sK1 sK1]
  have l21 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [← l20 sK2 sK1]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l10 sK2 sK1]
    conv => enter [1, 2]; rw [← l21 sK2 sK1]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l21 sK2 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 sK1]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l22 sK2 sK1]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK1 X0]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l25 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [← l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK1 X0]
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0]
  have l30 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l29 sK0 sK1 sK2 X0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l24 sK0 sK1 sK2]
  have l33 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l34 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41776 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [← l30 sK0 sK1 sK2 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l35 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l34 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l33 sK0 sK1 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) sK2]
  have l36 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 sK0 sK1 sK2 X0]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l27 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l38 x y z]

theorem Equation3322_4512_implies_Equation41786 (G : Type*) [Magma G] (h3322 : Equation3322 G) (h4512 : Equation4512 G) : Equation41786 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3322 X0 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h3322 (sK2 ◇ sK1) sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← h3322 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3322 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l3 sK1 sK2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← h3322 (sK0 ◇ sK1) sK1 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_41786_implies_Equation3322 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41786 : Equation41786 G) : Equation3322 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK1) X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41786 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1)))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41786 sK0 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ X1))) X3]
    conv => enter [1, 1]; rw [← h41786 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ X1)) X3]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l5 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l7 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l6 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41786 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41786 sK2 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l9 sK2 sK1]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 (sK2 ◇ sK1)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
  have l18 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h41786 X0 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [← l17 sK0 sK1 sK2]
  have l19 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l18 X0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l20 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l19 X0 sK2 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l21 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l20 X0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l7 X0 (sK2 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ sK1)]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK1 sK2]
  have l23 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2 sK1]
    conv => enter [1]; rw [← l21 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK1 sK1]
  have l24 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK1 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK2 ◇ sK1)]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l27 x y z]

theorem Equation3322_4512_implies_Equation41794 (G : Type*) [Magma G] (h3322 : Equation3322 G) (h4512 : Equation4512 G) : Equation41794 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3322 X0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h3322 (sK1 ◇ sK1) sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3322 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l0 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h3322 X0 sK1 sK1]
    conv => enter [1]; rw [l2 X0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l3 sK2 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_41794_implies_Equation3322 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41794 : Equation41794 G) : Equation3322 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41794 X1 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h41794 (X0 ◇ X0) X0 (X0 ◇ X0)]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41794 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h41794 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 sK1]
  have l7 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1 sK1]
    conv => enter [1]; rw [← l4 (sK2 ◇ sK1) sK1]
  have l8 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l4 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK2 sK1]
  have l10 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l7 sK2 sK1]
    conv => enter [1]; rw [← l9 sK2 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 sK1]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation3322_4512_implies_Equation41798 (G : Type*) [Magma G] (h3322 : Equation3322 G) (h4512 : Equation4512 G) : Equation41798 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h3322 X0 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h3322 (sK2 ◇ sK1) sK1 sK2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3322 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l2 sK2 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_41798_implies_Equation3322 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41798 : Equation41798 G) : Equation3322 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41798 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X0 ◇ sK1))]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h41798 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ (X0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41798 sK0 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 sK2 sK1 X0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (X0 ◇ (X0 ◇ sK1))]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l2 sK2 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK2 ◇ (sK2 ◇ sK1))]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK2 ◇ sK1) X0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 ((sK2 ◇ sK1) ◇ sK1)]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) X0]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) X0]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l10 sK0 sK1 sK2 ((sK2 ◇ sK1) ◇ X0)]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2 ((sK2 ◇ sK1) ◇ sK1)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation3322_4512_implies_Equation41802 (G : Type*) [Magma G] (h3322 : Equation3322 G) (h4512 : Equation4512 G) : Equation41802 G := by
  have l0 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X0 ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h3322 X0 (sK0 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h3322 (sK0 ◇ sK2) sK2 sK0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3322 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ sK2)]
  have l2 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK2) sK2]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l2 sK3 sK0 sK2]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ sK2))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_41802_implies_Equation3322 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41802 : Equation41802 G) : Equation3322 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41802 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [h41802 sK2 sK1 X0 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
  have l4 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l4 sK2 sK1 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation3326_4512_implies_Equation41807 (G : Type*) [Magma G] (h3326 : Equation3326 G) (h4512 : Equation4512 G) : Equation41807 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3326 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3326 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3326 sK0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h3326 x (x ◇ y) z]

theorem Equation4512_41807_implies_Equation3326 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41807 : Equation41807 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41807 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41807 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41807 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l2 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l4 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation3326_4512_implies_Equation41824 (G : Type*) [Magma G] (h3326 : Equation3326 G) (h4512 : Equation4512 G) : Equation41824 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h3326 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3326 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
  have l2 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h3326 sK2 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3326 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l2 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41824_implies_Equation3326 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41824 : Equation41824 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41824 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41824 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation3326_4512_implies_Equation41841 (G : Type*) [Magma G] (h3326 : Equation3326 G) (h4512 : Equation4512 G) : Equation41841 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3326 sK0 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3326 sK0 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [h3326 (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [h3326 (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK2 sK1]
  have l4 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [← h3326 sK2 (sK2 ◇ (sK0 ◇ sK1)) sK0]
  have l5 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h3326 sK2 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h3326 sK2 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK2 sK0 sK1]
  have l7 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h3326 sK2 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← l6 sK2 sK0 sK1]
  have l8 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l7 sK2 sK0 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← l8 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_41841_implies_Equation3326 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41841 : Equation41841 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41841 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41841 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h41841 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2, 2]; rw [h41841 sK2 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← h41841 sK0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41841 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK0 sK2 sK1]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41841 sK0 (sK2 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41841 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41841 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l10 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l5 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation3326_4512_implies_Equation41858 (G : Type*) [Magma G] (h3326 : Equation3326 G) (h4512 : Equation4512 G) : Equation41858 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3326 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [h3326 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 sK2]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [h3326 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l3 : ∀ sK1 sK3 sK0 sK2 X0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [h3326 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK3 sK0 sK2]
  have l4 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK3 sK0 sK2 sK3]
    conv => enter [1, 2]; rw [← h3326 sK3 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l5 : ∀ sK0 sK1 sK2 sK3 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l4 sK1 sK3 sK0 sK2]
  have l6 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK3]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 sK3]
  have l7 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [h3326 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2 sK3]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h3326 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_41858_implies_Equation3326 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41858 : Equation41858 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41858 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41858 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation3326_4512_implies_Equation41753 (G : Type*) [Magma G] (h3326 : Equation3326 G) (h4512 : Equation4512 G) : Equation41753 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3326 sK0 sK2 sK0]
    conv => enter [1, 2, 2]; rw [h3326 sK0 sK2 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3326 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3326 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41753_implies_Equation3326 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41753 : Equation41753 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41753 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41753 sK0 (X0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2]; rw [← h41753 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41753 sK0 (sK2 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2]; rw [← h41753 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation3370_4512_implies_Equation3350 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3350 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK2 ◇ sK2)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK2 ◇ sK2) sK0 sK0]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 sK2 sK2 sK2]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1, 2]; rw [l1 sK2 sK0]
  have l3 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h3370 sK0 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l0 sK0 sK2 (sK2 ◇ sK2)]
  have l4 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l3 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l1 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l5 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h3370 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l5 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [l2 sK0 sK2 (sK2 ◇ sK2)]
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l4 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l7 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation3350_4512_implies_Equation3370 (G : Type*) [Magma G] (h3350 : Equation3350 G) (h4512 : Equation4512 G) : Equation3370 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3350 X1 X2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3350 (X0 ◇ X0) X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation3370_4512_implies_Equation3364 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3364 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK2) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK2 sK0 sK0]
  have l1 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ (sK0 ◇ sK2)) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ sK2) sK2 sK2]
  have l2 : ∀ X0 sK0 sK2 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ sK2)) = (sK0 ◇ X0) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK2]
    conv => enter [1]; rw [← h3370 sK0 X0 sK2]
  have l3 : ∀ sK2 X0 sK0 : G, (sK2 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h3370 sK2 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l1 sK2 sK0 (sK0 ◇ sK2)]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l3 sK2 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))]
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l3 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l4 sK0 sK2]
  have l6 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [l5 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 sK2]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l2 X0 sK0 sK2]
    conv => enter [1, 2]; rw [← l6 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation3364_implies_Equation3370 (G : Type*) [Magma G] (h3364 : Equation3364 G) : Equation3370 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h3364 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3364 sK2 (sK2 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation3370_4512_implies_Equation3385 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3385 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ sK1)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3370 sK1 X0 sK0]
  have l2 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [← l1 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X1]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ sK2) sK0 sK0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK2 sK1 sK1]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3370 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK1]
  have l6 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h3370 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK2]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l8 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ sK0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ sK2) ◇ sK0)]
  have l9 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2 X1]
  have l10 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l6 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK1 ◇ sK2) ◇ sK2)]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h3370 X0 sK0 sK1]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l13 sK0 sK1 X0]
    conv => enter [1]; rw [l10 sK0 sK1 sK1 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 sK0]
    conv => enter [1]; rw [← l6 sK1 (sK0 ◇ sK1) sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0 sK1 sK2 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK0 sK2 sK1]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
  have l20 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3370 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l17 sK0 sK1]
  have l21 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l20 sK1 X0 sK0]
    conv => enter [1]; rw [l2 X0 (sK0 ◇ sK1) sK1 sK0]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l5 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK0 ◇ sK1) ◇ sK1)]
  have l23 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK1 sK2 (sK0 ◇ sK1) sK1]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l19 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK0 sK1 sK0 sK2]
  have l27 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK0]
    conv => enter [1]; rw [← l26 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l27 sK1 sK2 sK0]
  have l29 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l28 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← l23 sK1 sK0 sK2]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l29 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l31 x y z]

theorem Equation3385_4512_implies_Equation3370 (G : Type*) [Magma G] (h3385 : Equation3385 G) (h4512 : Equation4512 G) : Equation3370 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3385 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3385 X0 sK0 sK1]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h3385 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3385 X0 sK2 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3385 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 X0]
  have l4 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (((sK0 ◇ sK1) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h3385 X0 X1 ((sK0 ◇ sK1) ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 X1]
  have l5 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l4 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X1 (X0 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3385 X1 X0 (X0 ◇ X0)]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l6 (sK0 ◇ sK1) X0]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK2]
    conv => enter [1, 2]; rw [l6 sK0 sK2]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h3385 X0 X0 (sK0 ◇ sK1)]
  have l10 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h3385 (sK2 ◇ sK0) sK2 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK2]
  have l11 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l10 sK2 sK0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X0 X0]
    conv => enter [1]; rw [l9 X0 X0 X1]
  have l13 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l11 sK2 sK0]
    conv => enter [1, 2]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l12 sK1 X0]
  have l15 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l14 sK0 sK1 X0]
  have l16 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l13 sK2 sK0 sK2]
    conv => enter [1]; rw [← l15 sK1 sK0 sK2]
  have l17 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l16 sK2 sK0 sK1]
    conv => enter [1]; rw [← h3385 sK1 sK0 sK1]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

theorem Equation3370_4512_implies_Equation3398 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3398 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ sK2) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 sK2 sK0 sK0]
  have l1 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ (sK0 ◇ sK2)) sK2 sK2]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h3370 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l0 sK0 sK2 sK2]
  have l3 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [h3370 sK2 X0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l1 sK2 sK1 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l4 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l3 sK2 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l5 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 sK2 sK0]
    conv => enter [1]; rw [← l3 sK2 (sK0 ◇ sK2) sK0 sK0]
  have l6 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ sK2) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK2 sK2]
    conv => enter [1]; rw [l5 sK0 sK2]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l2 sK0 X0 sK2]
    conv => enter [1, 2]; rw [l6 sK0 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l3 sK2 (sK0 ◇ sK2) sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l3 sK2 (sK1 ◇ (sK0 ◇ sK2)) sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation3398_4512_implies_Equation3370 (G : Type*) [Magma G] (h3398 : Equation3398 G) (h4512 : Equation4512 G) : Equation3370 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3398 X1 X2 (X0 ◇ X2)]
    conv => enter [1, 2]; rw [← h3398 X0 X1 X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X0 X2 (X0 ◇ X1)]
  have l2 : ∀ X0 sK0 sK2 : G, (X0 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK2 ◇ X0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h3398 X0 sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3398 sK2 X0 sK0]
  have l3 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h3398 sK2 (sK2 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l2 X0 sK0 sK2]
  have l4 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l3 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l5 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l4 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ sK0))]
  have l6 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((X1 ◇ sK0) ◇ X1) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l5 sK2 sK0 sK2 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ sK0) X1 sK2]
  have l7 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK0 ◇ X1)) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l6 sK2 sK0 X1]
    conv => enter [1]; rw [← h4512 X1 sK0 X1]
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h3398 sK0 X0 X0]
    conv => enter [1, 2]; rw [← l7 sK2 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation3370_4512_implies_Equation3404 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3404 G := by
  have l0 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 (sK1 ◇ (sK2 ◇ sK0)) sK2 sK2]
  have l1 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [h3370 sK2 X0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK2 sK1 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK2 (sK2 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2 (sK1 ◇ (sK2 ◇ sK0)) sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3370 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation3404_4512_implies_Equation3370 (G : Type*) [Magma G] (h3404 : Equation3404 G) (h4512 : Equation4512 G) : Equation3370 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X3) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h3404 (X1 ◇ (X2 ◇ X0)) X3 X2]
    conv => enter [1, 2, 2]; rw [← h3404 X0 X1 X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ ((X2 ◇ X0) ◇ X3)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l0 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 X3]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK1) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h3404 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1 X0]
    conv => enter [1, 2]; rw [← h3404 (sK2 ◇ (sK2 ◇ sK0)) X0 sK1]
  have l4 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ sK2) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ sK0) sK2 X0]
    conv => enter [1, 2]; rw [← h3404 sK0 X0 sK2]
  have l5 : ∀ X0 sK2 sK0 X1 : G, ((X0 ◇ (sK2 ◇ sK0)) ◇ X1) = (sK2 ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [h3404 (X0 ◇ (sK2 ◇ sK0)) X1 sK2]
    conv => enter [1, 2, 2]; rw [← h3404 sK0 X0 sK2]
  have l6 : ∀ sK2 X1 sK0 X0 : G, (sK2 ◇ (X1 ◇ (sK0 ◇ X0))) = (X0 ◇ ((sK2 ◇ sK0) ◇ X1)) := by
    intro sK2 X1 sK0 X0
    conv => enter [1]; rw [← l5 X0 sK2 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK0) X1]
  have l7 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK2 ◇ sK0)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← h3404 sK0 sK2 sK2]
  have l8 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l7 sK2 sK0 X0]
    conv => enter [1]; rw [l6 sK2 X0 sK0 sK2]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h3404 sK0 (sK2 ◇ sK0) sK2]
    conv => enter [1]; rw [← l8 sK2 sK0 (sK2 ◇ sK0)]
  have l10 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l8 sK2 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← h3404 (sK2 ◇ sK0) (sK2 ◇ sK0) sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK1) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK0 sK2]
  have l12 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h3404 sK0 (sK2 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [← l9 sK0 sK2]
  have l13 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h3404 sK0 sK0 sK2]
    conv => enter [1]; rw [← l12 sK0 sK2]
  have l14 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK1) = ((sK2 ◇ sK0) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 sK2 sK0 (sK2 ◇ sK0)]
  have l15 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l14 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
  have l16 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h3404 (sK2 ◇ sK0) (sK2 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [l10 sK2 sK0]
  have l17 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h3404 sK0 (sK2 ◇ sK0) sK2]
    conv => enter [1]; rw [← l16 sK2 sK0]
  have l18 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ (sK2 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l13 sK0 sK2]
  have l19 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l18 sK2 sK0 X0]
    conv => enter [1]; rw [← h3404 sK0 X0 sK0]
  have l20 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h3404 (sK2 ◇ sK0) (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← l17 sK0 sK2]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h3404 sK0 sK0 sK2]
    conv => enter [1]; rw [← l20 sK2 sK0]
  have l22 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h3404 (sK2 ◇ sK0) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l21 sK0 sK2]
  have l23 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l22 sK2 sK0 X0]
    conv => enter [1]; rw [l2 (sK2 ◇ sK0) X0 sK0 sK0]
  have l24 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h3404 X0 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [← l23 sK2 sK0 X0]
  have l25 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l24 sK2 sK2 sK0]
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
  have l26 : ∀ X0 sK2 sK0 X1 sK1 : G, (X0 ◇ (((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1)) = (((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK1) ◇ X1) := by
    intro X0 sK2 sK0 X1 sK1
    conv => enter [1]; rw [h4512 X0 ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l3 sK1 sK2 sK0 X0]
  have l27 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 1]; rw [l25 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l28 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1 X0]
    conv => enter [1, 1]; rw [l15 sK1 sK2 sK0]
  have l29 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l28 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l30 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l19 sK0 sK0 X0]
    conv => enter [1]; rw [l27 sK0 sK0 X0 sK1]
  have l31 : ∀ X0 sK2 sK0 X1 sK1 : G, (X0 ◇ (((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ X1)) := by
    intro X0 sK2 sK0 X1 sK1
    conv => enter [1]; rw [l26 X0 sK2 sK0 X1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1 X1]
  have l32 : ∀ X0 sK2 sK0 X1 sK1 : G, (X0 ◇ (((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X0 sK2 sK0 X1 sK1
    conv => enter [1]; rw [l31 X0 sK2 sK0 X1 sK1]
    conv => enter [1]; rw [l29 sK1 sK2 sK0 X1]
  have l33 : ∀ sK0 X1 X0 sK2 : G, (sK0 ◇ X1) = (X0 ◇ (((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0 sK2
    conv => enter [1]; rw [l30 sK0 X1 sK0]
    conv => enter [1]; rw [← l32 X0 sK2 sK0 X1 sK0]
  have l34 : ∀ sK0 X1 X0 sK2 : G, (sK0 ◇ X1) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0 sK2
    conv => enter [1]; rw [l33 sK0 X1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK0)) X0 X1]
  have l35 : ∀ sK0 X1 sK2 : G, (sK0 ◇ X1) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [l34 sK0 X1 sK0 sK2]
    conv => enter [1]; rw [← h3404 X1 (sK2 ◇ (sK2 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

theorem Equation3370_4512_implies_Equation3417 (G : Type*) [Magma G] (h3370 : Equation3370 G) (h4512 : Equation4512 G) : Equation3417 G := by
  have l0 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3370 (sK1 ◇ sK2) X0 sK0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 sK0]
    conv => enter [1, 2]; rw [← h3370 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1, 2]; rw [← h3370 sK2 sK1 sK1]
  have l3 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h3370 (sK1 ◇ sK2) X0 sK0]
    conv => enter [1]; rw [l2 sK1 sK2 X0]
  have l4 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) = ((sK2 ◇ sK1) ◇ X1) := by
    intro X1 X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← h3370 (sK2 ◇ sK1) X1 X0]
  have l5 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = ((sK2 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X1 sK0]
    conv => enter [1]; rw [l4 X1 sK0 sK1 sK2]
  have l6 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [h3370 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l3 sK2 sK0 sK1 sK2]
  have l7 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h3370 (sK2 ◇ sK1) X0 sK2]
    conv => enter [1, 2]; rw [← h3370 sK1 sK2 sK2]
  have l8 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X1 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X1 X0]
    conv => enter [1, 2, 2]; rw [← l7 sK2 sK1 X0]
  have l9 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l7 sK2 sK1 X0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X0]
  have l10 : ∀ sK1 sK2 X1 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro sK1 sK2 X1 X0 sK0
    conv => enter [1]; rw [l8 sK1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1 sK2 X0]
  have l11 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h3370 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l12 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ X1) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h3370 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) X1 X0]
  have l13 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X1)) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [l12 X1 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X1]
  have l14 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l9 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2 sK0]
  have l15 : ∀ sK1 sK2 X1 sK0 : G, ((sK1 ◇ sK2) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X1)) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [l10 sK1 sK2 X1 sK1 sK0]
    conv => enter [1]; rw [l13 X1 sK1 sK0 sK1 sK2]
  have l16 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [← l14 sK0 sK0 sK1 sK2]
  have l17 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [h3370 (sK0 ◇ X0) X1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l15 sK1 sK2 X0 sK0]
  have l18 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l17 sK0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 X0 X1]
  have l19 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l16 sK1 sK2 sK0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [← l19 sK1 sK2 sK0]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) sK0 sK0]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2]; rw [← l21 sK0 sK1 sK2]
  have l23 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [← h3370 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 sK0]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h3370 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l15 sK1 sK2 (sK1 ◇ sK2) sK0]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l24 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l18 X0 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l26 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) X0 sK0]
    conv => enter [1]; rw [l23 X0 sK0 sK1 sK2]
  have l27 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l26 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← l9 X0 sK1 sK2 sK1]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l27 sK1 sK2 X0]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l14 sK0 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
  have l30 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l15 sK1 sK2 ((sK1 ◇ sK2) ◇ X0) sK0]
    conv => enter [1, 2]; rw [← l25 sK0 sK1 sK2 X0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [← l30 sK1 sK2 (sK1 ◇ sK2) sK0]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l22 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
  have l34 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l27 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l35 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l6 sK1 sK1 sK2 sK0]
  have l36 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [h3370 (sK1 ◇ sK2) (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [l35 sK1 sK2 sK1]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l36 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [l34 sK1 sK2 sK1 sK1]
  have l39 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h3370 sK2 sK1 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l39 x y z]

theorem Equation3417_4512_implies_Equation3370 (G : Type*) [Magma G] (h3417 : Equation3417 G) (h4512 : Equation4512 G) : Equation3370 G := by
  have l0 : ∀ X1 sK0 sK1 X0 : G, ((X1 ◇ (sK0 ◇ sK1)) ◇ X1) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h3417 (X1 ◇ (sK0 ◇ sK1)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3417 sK1 sK0 X1]
  have l1 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = ((X1 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [h3417 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 X1 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 X1]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK1) X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h3417 sK1 sK0 (sK0 ◇ sK1)]
  have l4 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (((sK0 ◇ sK1) ◇ X1) ◇ X1) := by
    intro X0 sK0 sK1 X1
    conv => enter [1, 2, 2]; rw [l2 sK0 sK1 X1]
    conv => enter [1]; rw [← h3417 ((sK0 ◇ sK1) ◇ X1) X1 X0]
  have l5 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X1 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l4 X0 sK0 sK1 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X1 X1]
  have l6 : ∀ sK1 sK0 X1 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (X1 ◇ X1)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [h3417 sK1 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0 sK1 X1]
  have l7 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0 X1]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3417 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l3 sK1 sK0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h3417 X0 X0 (sK0 ◇ sK1)]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h3417 (sK0 ◇ sK1) X0 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l9 X1 X1 X1]
    conv => enter [1]; rw [l9 X1 X1 X0]
  have l12 : ∀ X1 sK1 sK2 sK0 X0 : G, ((X1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X1) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1))) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h3417 (X1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3417 (sK2 ◇ (sK2 ◇ sK0)) sK1 X1]
  have l13 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((X1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X1) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [h3417 sK1 (sK2 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l12 X1 sK1 sK2 sK0 sK1]
  have l14 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X1)) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l13 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [← h4512 X1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) X1]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [l11 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l14 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← h3417 (sK2 ◇ (sK2 ◇ sK0)) sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l17 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h3417 sK1 (sK2 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l16 sK1 sK2 sK0]
  have l18 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l17 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h3417 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0 X0]
  have l19 : ∀ X1 sK2 sK0 X0 : G, ((X1 ◇ (sK2 ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [h3417 (X1 ◇ (sK2 ◇ sK0)) X1 X0]
    conv => enter [1, 2, 2]; rw [← h3417 sK0 sK2 X1]
  have l20 : ∀ sK2 sK0 X1 : G, (sK2 ◇ sK0) = ((X1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [h3417 sK2 sK0 sK2]
    conv => enter [1]; rw [← l19 X1 sK2 sK0 sK2]
  have l21 : ∀ sK2 sK0 X1 : G, (sK2 ◇ sK0) = (X1 ◇ ((sK2 ◇ sK0) ◇ X1)) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l20 sK2 sK0 X1]
    conv => enter [1]; rw [← h4512 X1 (sK2 ◇ sK0) X1]
  have l22 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l21 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l11 (sK2 ◇ sK0) X0]
  have l23 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = (sK0 ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [l21 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← h3417 sK0 sK2 (sK2 ◇ sK0)]
  have l24 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = ((X0 ◇ X0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l21 sK2 sK0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l22 sK2 sK0 X0]
  have l25 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l24 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (sK2 ◇ sK0)]
  have l26 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro X0 sK2 sK0
    conv => enter [1, 2]; rw [l25 sK2 sK0 X0]
    conv => enter [1]; rw [← h3417 (sK2 ◇ sK0) X0 X0]
  have l27 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK2 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h3417 (sK2 ◇ (sK2 ◇ sK0)) X0 X0]
    conv => enter [1, 2]; rw [← h3417 (sK2 ◇ sK0) sK2 X0]
  have l28 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro X0 sK2 sK0
    conv => enter [1, 2]; rw [l26 sK2 sK2 sK0]
    conv => enter [1]; rw [← l27 sK2 sK0 X0]
  have l29 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l26 sK2 sK2 sK0]
    conv => enter [1]; rw [h3417 (sK2 ◇ sK0) sK2 sK1]
  have l30 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1, 1]; rw [l23 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
  have l31 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l10 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l32 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [← l28 (X0 ◇ X1) sK2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK2 ◇ sK0))]
  have l33 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← l18 (X0 ◇ X1) sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l29 sK2 sK0 sK1]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h3417 (sK2 ◇ sK0) sK2 sK1]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l26 sK2 sK2 sK0]
  have l37 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l30 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l36 sK0 sK1 sK2]
  have l38 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l37 sK2 sK0 sK1]
    conv => enter [1]; rw [l31 sK0 sK1 sK1 (sK2 ◇ (sK2 ◇ sK0))]
  have l39 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l38 sK2 sK0 sK1]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l39 sK1 sK2 sK0]
  have l41 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [← l18 (sK0 ◇ sK1) sK1 sK2 sK0]
  have l42 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK2 ◇ sK0))]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 sK2 sK0 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l18 (sK2 ◇ (sK2 ◇ sK0)) sK1 sK2 sK0]
  have l46 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l42 sK0 sK1 sK2]
  have l47 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l46 sK1 sK2 sK0]
    conv => enter [1]; rw [l33 sK1 sK2 sK0 sK0 (sK2 ◇ (sK2 ◇ sK0))]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
    conv => enter [1]; rw [← l47 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l48 x y z]

@[equational_result]
theorem Equation4268_implies_Equation4282 (G : Type*) [Magma G] (h4268 : Equation4268 G) : Equation4282 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4268 sK0 sK2]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4268 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4282_implies_Equation4268 (G : Type*) [Magma G] (h4282 : Equation4282 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [h4282 x x y]

@[equational_result]
theorem Equation4268_implies_Equation53865 (G : Type*) [Magma G] (h4268 : Equation4268 G) : Equation53865 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 (sK2 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_53865_implies_Equation4268 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53865 : Equation53865 G) : Equation4268 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53865 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0]
  intro x y
  conv => enter [1]; rw [← l9 x y]

@[equational_result]
theorem Equation4268_implies_Equation53867 (G : Type*) [Magma G] (h4268 : Equation4268 G) : Equation53867 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4268 sK0 sK1]
    conv => enter [1]; rw [h4268 sK0 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_53867_implies_Equation4268 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53867 : Equation53867 G) : Equation4268 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53867 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0]
  intro x y
  conv => enter [1]; rw [← l9 x y]

@[equational_result]
theorem Equation4268_implies_Equation53868 (G : Type*) [Magma G] (h4268 : Equation4268 G) : Equation53868 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4268 sK1 sK2]
    conv => enter [1]; rw [h4268 sK1 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_53868_implies_Equation4268 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53868 : Equation53868 G) : Equation4268 G := by
  have l0 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h53868 sK0 X2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l1 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 sK0 X0 X1 X2]
  have l2 : ∀ sK0 X0 X3 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X3) := by
    intro sK0 X0 X3
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 X3]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation4268_implies_Equation53859 (G : Type*) [Magma G] (h4268 : Equation4268 G) : Equation53859 G := by
  intro x y
  conv => enter [1]; rw [← h4268 x y]
  conv => enter [1]; rw [h4268 x (x ◇ x)]

theorem Equation4512_53859_implies_Equation4268 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53859 : Equation53859 G) : Equation4268 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h53859 X0 X1]
    conv => enter [1, 2]; rw [h53859 X0 X0]
    conv => enter [1, 2]; rw [← h53859 X0 X1]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53859 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h53859 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← h53859 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation4268_implies_Equation53861 (G : Type*) [Magma G] (h4268 : Equation4268 G) : Equation53861 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4268 sK0 sK2]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4268 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4268 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4268 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l2 x z y]

theorem Equation4512_53861_implies_Equation4268 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation4268 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53861 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l1 sK0 sK0 X0]
    conv => enter [1]; rw [l1 sK0 sK0 X2]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

end Semigroup5
