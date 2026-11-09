import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation4512_41649_implies_Equation41530 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41530 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l1 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l3 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l1 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l2 sK0 (X2 ◇ (X2 ◇ X3)) sK0]
  have l4 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X3)) := by
    intro sK0 X3
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0) X3]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) X3 sK0]
  have l5 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X3) := by
    intro sK0 X3
    conv => enter [1]; rw [l4 sK0 X3]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) X3 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation43_4512_41649_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41532 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK1]
  have l5 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l1 sK1 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l7 : ∀ sK0 X2 X3 sK1 : G, (sK0 ◇ sK0) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 X2 X3 sK1
    conv => enter [1]; rw [l6 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l4 sK0 (X2 ◇ (X2 ◇ X3)) sK1]
  have l8 : ∀ sK0 sK1 X2 X3 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 X2 X3
    conv => enter [1]; rw [l7 sK0 X2 X3 sK1]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK1 ◇ sK1)]
  have l9 : ∀ sK0 sK1 X3 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (X3 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X3
    conv => enter [1]; rw [l8 sK0 sK1 sK0 X3]
    conv => enter [1, 2]; rw [l4 sK0 X3 sK1]
  have l10 : ∀ sK0 X3 sK1 : G, (sK0 ◇ sK0) = (X3 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X3 sK1
    conv => enter [1]; rw [l9 sK0 sK1 X3]
    conv => enter [1]; rw [← l5 X3 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X3
    conv => enter [1]; rw [l10 sK0 X3 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation43_4512_41649_implies_Equation41533 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41533 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK0]
  have l5 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l7 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l6 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l4 sK0 (X2 ◇ (X2 ◇ X3)) sK0]
  have l8 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l7 sK0 X2 X3]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X3
    conv => enter [1]; rw [l8 sK0 sK0 X3]
    conv => enter [1, 2]; rw [l4 sK0 X3 sK0]
  have l10 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X3
    conv => enter [1]; rw [l9 sK0 X3]
    conv => enter [1]; rw [← l5 X3 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l10 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation43_4512_41649_implies_Equation41539 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41539 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK0]
  have l5 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l7 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l6 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l4 sK0 (X2 ◇ (X2 ◇ X3)) sK0]
  have l8 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l7 sK0 X2 X3]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X3
    conv => enter [1]; rw [l8 sK0 sK0 X3]
    conv => enter [1, 2]; rw [l4 sK0 X3 sK0]
  have l10 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X3
    conv => enter [1]; rw [l9 sK0 X3]
    conv => enter [1]; rw [← l5 X3 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation43_4512_41649_implies_Equation41543 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41543 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK1]
  have l5 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l1 sK1 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ sK1 X1 X2 X3 : G, (sK1 ◇ sK1) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK1 X1 X2 X3
    conv => enter [1]; rw [h41649 sK1 X1 X2 X3]
  have l7 : ∀ sK1 X2 X3 : G, (sK1 ◇ sK1) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [l6 sK1 sK1 X2 X3]
    conv => enter [1]; rw [l4 sK1 (X2 ◇ (X2 ◇ X3)) sK1]
  have l8 : ∀ sK1 X2 X3 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [l7 sK1 X2 X3]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK1 ◇ sK1)]
  have l9 : ∀ sK1 X3 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X3 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X3
    conv => enter [1]; rw [l8 sK1 sK1 X3]
    conv => enter [1, 2]; rw [l4 sK1 X3 sK1]
  have l10 : ∀ sK1 X3 : G, (sK1 ◇ sK1) = (X3 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X3
    conv => enter [1]; rw [l9 sK1 X3]
    conv => enter [1]; rw [← l5 X3 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation43_4512_41649_implies_Equation41558 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41558 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l4 X1 sK1]
  have l7 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [← l4 X1 sK1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l8 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ sK0 X2 X3 sK1 : G, (sK0 ◇ sK0) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X2 X3 sK1
    conv => enter [1]; rw [l8 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l6 sK0 (X2 ◇ (X2 ◇ X3)) sK1]
  have l11 : ∀ sK0 sK1 X2 X3 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 X2 X3
    conv => enter [1]; rw [l10 sK0 X2 X3 sK1]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK0 sK1 X3 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X3 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X3
    conv => enter [1]; rw [l11 sK0 sK1 sK0 X3]
    conv => enter [1, 2]; rw [l6 sK0 X3 sK1]
  have l13 : ∀ sK0 X3 sK1 : G, (sK0 ◇ sK0) = (X3 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X3 sK1
    conv => enter [1]; rw [l12 sK0 sK1 X3]
    conv => enter [1]; rw [← l7 X3 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l14 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X3
    conv => enter [1]; rw [l13 sK0 X3 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation43_4512_41649_implies_Equation41559 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41559 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41649 X1 X2 X2 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [← h41649 X0 X2 X2 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l2 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l4 X1 X2 X1]
    conv => enter [1, 2]; rw [l2 X1 sK0]
  have l6 : ∀ X2 X1 sK0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X2 X1 sK0
    conv => enter [1]; rw [← l3 X1 X2 X2]
    conv => enter [1, 2]; rw [l2 X2 sK0]
  have l7 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l8 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l7 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l5 sK0 (X2 ◇ (X2 ◇ X3)) sK0]
  have l9 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l8 sK0 X2 X3]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X3
    conv => enter [1]; rw [l9 sK0 sK0 X3]
    conv => enter [1, 2]; rw [l5 sK0 X3 sK0]
  have l11 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X3
    conv => enter [1]; rw [l10 sK0 X3]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) X3 sK0]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l13 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l12 sK0 X2 X1]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [l15 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation43_4512_41649_implies_Equation41562 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41562 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK2]
  have l5 : ∀ X1 sK2 X2 : G, (X1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK2 X2
    conv => enter [1, 2]; rw [l1 sK2 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l7 : ∀ sK0 X2 X3 sK2 : G, (sK0 ◇ sK0) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 X2 X3 sK2
    conv => enter [1]; rw [l6 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l4 sK0 (X2 ◇ (X2 ◇ X3)) sK2]
  have l8 : ∀ sK0 sK2 X2 X3 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 sK2 X2 X3
    conv => enter [1]; rw [l7 sK0 X2 X3 sK2]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK2 ◇ sK2)]
  have l9 : ∀ sK0 sK2 X3 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X3 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X3
    conv => enter [1]; rw [l8 sK0 sK2 sK0 X3]
    conv => enter [1, 2]; rw [l4 sK0 X3 sK2]
  have l10 : ∀ sK0 X3 sK2 : G, (sK0 ◇ sK0) = (X3 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X3 sK2
    conv => enter [1]; rw [l9 sK0 sK2 X3]
    conv => enter [1]; rw [← l5 X3 sK2 (sK2 ◇ sK2)]
  have l11 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X3
    conv => enter [1]; rw [l10 sK0 X3 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation43_4512_41649_implies_Equation41563 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41563 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l3 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
  have l4 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l3 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK3 ◇ sK0)]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X1 X2]
    conv => enter [1, 2]; rw [l6 X1 X0]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l5 X2 X1 X1]
  have l9 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X0 ◇ X0) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← l4 sK2 sK3 sK0]
    conv => enter [1]; rw [l6 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l10 : ∀ X1 X2 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← l8 X2 X1 X1]
    conv => enter [1, 2]; rw [l6 X1 sK1]
  have l11 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l7 X1 X2 X1]
    conv => enter [1, 2]; rw [l6 X1 sK1]
  have l12 : ∀ sK1 X1 X2 X3 : G, (sK1 ◇ sK1) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK1 X1 X2 X3
    conv => enter [1]; rw [h41649 sK1 X1 X2 X3]
  have l13 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ sK1) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l6 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l4 sK2 sK3 sK0]
  have l14 : ∀ sK1 X2 X3 : G, (sK1 ◇ sK1) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [l12 sK1 sK1 X2 X3]
    conv => enter [1]; rw [l11 sK1 (X2 ◇ (X2 ◇ X3)) sK1]
  have l15 : ∀ sK1 X2 X3 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [l14 sK1 X2 X3]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK1 ◇ sK1)]
  have l16 : ∀ sK1 X3 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X3 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X3
    conv => enter [1]; rw [l15 sK1 sK1 X3]
    conv => enter [1, 2]; rw [l11 sK1 X3 sK1]
  have l17 : ∀ sK1 X3 : G, (sK1 ◇ sK1) = (X3 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X3
    conv => enter [1]; rw [l16 sK1 X3]
    conv => enter [1]; rw [l10 (sK1 ◇ sK1) X3 sK1]
  have l18 : ∀ X0 sK1 sK3 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro X0 sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l13 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l1 (sK3 ◇ sK0) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l19 : ∀ sK1 sK3 sK0 sK2 X0 : G, (sK1 ◇ sK1) = ((sK3 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l17 sK1 X0]
    conv => enter [1]; rw [l18 X0 sK1 sK3 sK0 sK2]
  have l20 : ∀ X0 X1 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X1) := by
    intro X0 X1 sK3 sK0 sK2
    conv => enter [1]; rw [← l0 X0 X0 X1]
    conv => enter [1, 1]; rw [← l9 sK3 sK0 sK2 X0]
  have l21 : ∀ X0 X1 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X1)) := by
    intro X0 X1 sK3 sK0 sK2
    conv => enter [1]; rw [l20 X0 X1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK0) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X1]
  have l22 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l19 sK1 sK1 sK1 sK1 X1]
    conv => enter [1]; rw [← l21 X0 X1 sK1 sK1 sK1]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l17 sK1 sK1]
    conv => enter [1, 2]; rw [l22 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l23 x y z w]

theorem Equation43_4512_41649_implies_Equation41632 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41632 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l4 X1 sK1]
  have l6 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [← l4 X1 sK1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l7 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK0 X2 X3 sK1 : G, (sK0 ◇ sK0) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X2 X3 sK1
    conv => enter [1]; rw [l7 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l5 sK0 (X2 ◇ (X2 ◇ X3)) sK1]
  have l10 : ∀ sK0 sK1 X2 X3 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 X2 X3
    conv => enter [1]; rw [l9 sK0 X2 X3 sK1]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l11 : ∀ sK0 sK1 X3 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X3 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X3
    conv => enter [1]; rw [l10 sK0 sK1 sK0 X3]
    conv => enter [1, 2]; rw [l5 sK0 X3 sK1]
  have l12 : ∀ sK0 X3 sK1 : G, (sK0 ◇ sK0) = (X3 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X3 sK1
    conv => enter [1]; rw [l11 sK0 sK1 X3]
    conv => enter [1]; rw [← l6 X3 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l13 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X3
    conv => enter [1]; rw [l12 sK0 X3 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation43_4512_41649_implies_Equation41633 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41633 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41649 X1 X2 X2 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [← h41649 X0 X2 X2 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l2 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l4 X1 X2 X1]
    conv => enter [1, 2]; rw [l2 X1 sK0]
  have l6 : ∀ X2 X1 sK0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X2 X1 sK0
    conv => enter [1]; rw [← l3 X1 X2 X2]
    conv => enter [1, 2]; rw [l2 X2 sK0]
  have l7 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l8 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l7 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l5 sK0 (X2 ◇ (X2 ◇ X3)) sK0]
  have l9 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l8 sK0 X2 X3]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X3
    conv => enter [1]; rw [l9 sK0 sK0 X3]
    conv => enter [1, 2]; rw [l5 sK0 X3 sK0]
  have l11 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X3
    conv => enter [1]; rw [l10 sK0 X3]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) X3 sK0]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l13 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l12 sK0 X2 X1]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l15 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation43_4512_41649_implies_Equation41636 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41636 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK2]
  have l5 : ∀ X1 sK2 X2 : G, (X1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK2 X2
    conv => enter [1, 2]; rw [l1 sK2 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41649 sK0 X1 X2 X3]
  have l7 : ∀ sK0 X2 X3 sK2 : G, (sK0 ◇ sK0) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 X2 X3 sK2
    conv => enter [1]; rw [l6 sK0 sK0 X2 X3]
    conv => enter [1]; rw [l4 sK0 (X2 ◇ (X2 ◇ X3)) sK2]
  have l8 : ∀ sK0 sK2 X2 X3 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK0 sK2 X2 X3
    conv => enter [1]; rw [l7 sK0 X2 X3 sK2]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK2 ◇ sK2)]
  have l9 : ∀ sK0 sK2 X3 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X3 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X3
    conv => enter [1]; rw [l8 sK0 sK2 sK0 X3]
    conv => enter [1, 2]; rw [l4 sK0 X3 sK2]
  have l10 : ∀ sK0 X3 sK2 : G, (sK0 ◇ sK0) = (X3 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X3 sK2
    conv => enter [1]; rw [l9 sK0 sK2 X3]
    conv => enter [1]; rw [← l5 X3 sK2 (sK2 ◇ sK2)]
  have l11 : ∀ sK0 X3 : G, (sK0 ◇ sK0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X3
    conv => enter [1]; rw [l10 sK0 X3 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation43_4512_41649_implies_Equation41637 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41637 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l3 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
  have l4 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l3 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK3 ◇ sK0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l5 X0 X2]
    conv => enter [1]; rw [l1 X1 X2 X2]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X1 X2]
    conv => enter [1, 2]; rw [l5 X1 X0]
  have l8 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X0 ◇ X0) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← l4 sK2 sK3 sK0]
    conv => enter [1]; rw [l5 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l9 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l7 X1 X2 X1]
    conv => enter [1, 2]; rw [l5 X1 sK1]
  have l10 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l5 sK1 X1]
    conv => enter [1]; rw [l6 X1 X1 X2]
  have l11 : ∀ sK1 X1 X2 X3 : G, (sK1 ◇ sK1) = (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro sK1 X1 X2 X3
    conv => enter [1]; rw [h41649 sK1 X1 X2 X3]
  have l12 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ sK1) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l5 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l4 sK2 sK3 sK0]
  have l13 : ∀ sK1 X2 X3 : G, (sK1 ◇ sK1) = ((X2 ◇ (X2 ◇ X3)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [l11 sK1 sK1 X2 X3]
    conv => enter [1]; rw [l9 sK1 (X2 ◇ (X2 ◇ X3)) sK1]
  have l14 : ∀ sK1 X2 X3 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [l13 sK1 X2 X3]
    conv => enter [1]; rw [h43 (X2 ◇ (X2 ◇ X3)) (sK1 ◇ sK1)]
  have l15 : ∀ sK1 X3 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X3 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X3
    conv => enter [1]; rw [l14 sK1 sK1 X3]
    conv => enter [1, 2]; rw [l9 sK1 X3 sK1]
  have l16 : ∀ sK1 X3 : G, (sK1 ◇ sK1) = (X3 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X3
    conv => enter [1]; rw [l15 sK1 X3]
    conv => enter [1]; rw [← l10 X3 sK1 (sK1 ◇ sK1)]
  have l17 : ∀ X0 sK1 sK3 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro X0 sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l12 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l1 (sK3 ◇ sK0) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l18 : ∀ sK1 sK3 sK0 sK2 X0 : G, (sK1 ◇ sK1) = ((sK3 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l16 sK1 X0]
    conv => enter [1]; rw [l17 X0 sK1 sK3 sK0 sK2]
  have l19 : ∀ X0 X1 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X1) := by
    intro X0 X1 sK3 sK0 sK2
    conv => enter [1]; rw [← l0 X0 X0 X1]
    conv => enter [1, 1]; rw [← l8 sK3 sK0 sK2 X0]
  have l20 : ∀ X0 X1 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X1)) := by
    intro X0 X1 sK3 sK0 sK2
    conv => enter [1]; rw [l19 X0 X1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK0) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X1]
  have l21 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l18 sK1 sK1 sK1 sK1 X1]
    conv => enter [1]; rw [← l20 X0 X1 sK1 sK1 sK1]
  have l22 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1, 2]; rw [l21 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l22 x y z w]

theorem Equation43_4512_41649_implies_Equation41654 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41649 : Equation41649 G) : Equation41654 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41649 X1 X2 X2 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [← h41649 X0 X2 X2 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41649 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41649 X0 X1 X1 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ sK2 X2 X1 : G, (sK2 ◇ sK2) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK2 X2 X1
    conv => enter [1]; rw [l3 sK2 X2 X1]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l0 sK3 (sK4 ◇ (sK1 ◇ sK0)) sK3]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

theorem Equation43_4512_41637_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation308 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X2 X1 X1]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← l4 X2 X1 X1]
    conv => enter [1, 2]; rw [l3 X1 sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l7 : ∀ X1 X0 X3 X2 : G, (X1 ◇ (X0 ◇ X0)) = ((X3 ◇ X3) ◇ (X2 ◇ X1)) := by
    intro X1 X0 X3 X2
    conv => enter [1, 2]; rw [l2 X0 X2 X3]
    conv => enter [1]; rw [l1 X1 X2 (X3 ◇ X3)]
  have l8 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (X1 ◇ X1)) := by
    intro sK0 X0 sK1 X1
    conv => enter [1, 2]; rw [l2 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X1 ◇ X1)]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l8 sK0 X0 sK1 sK0]
  have l10 : ∀ X1 X0 X3 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X3 ◇ (X3 ◇ (X2 ◇ X1))) := by
    intro X1 X0 X3 X2
    conv => enter [1]; rw [l7 X1 X0 X3 X2]
    conv => enter [1]; rw [← h4512 X3 X3 (X2 ◇ X1)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1 sK0]
  have l13 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l10 X1 X0 X1 X2]
    conv => enter [1]; rw [l5 X1 (X2 ◇ X1) sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l15 : ∀ X1 X0 sK0 X2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X1)) := by
    intro X1 X0 sK0 X2
    conv => enter [1]; rw [l13 X1 X0 X2 sK0]
    conv => enter [1]; rw [h43 (X2 ◇ X1) (sK0 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l17 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X1)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l3 sK0 X1]
    conv => enter [1]; rw [l15 X1 X1 sK0 X2]
  have l18 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ X1)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l11 sK0 X1]
    conv => enter [1]; rw [l17 X1 sK0 X2]
  have l19 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l19 sK0 X0 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation43_4512_41637_implies_Equation41530 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41530 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l9 (sK0 ◇ sK1) X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l9 sK1 X0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l9 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l12 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK1)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1)]
  have l21 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l22 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X1)) := by
    intro sK0 X0 sK1 X1
    conv => enter [1, 2]; rw [l8 X0 (sK0 ◇ sK1) X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X1 ◇ X1)]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l22 sK0 X0 sK1 sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0 sK0]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1]; rw [← l29 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l30 x y]

theorem Equation43_4512_41637_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41532 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 1]; rw [l1 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_41637_implies_Equation41533 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41533 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l2 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l6 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X1)) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l1 X0 (sK1 ◇ sK2) X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X1 ◇ X1)]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l6 sK0 X0 sK1 sK2 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation43_4512_41637_implies_Equation41539 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41539 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l2 X1 X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l2 X1 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l2 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l8 : ∀ X1 X0 X3 X2 : G, (X1 ◇ (X0 ◇ X0)) = ((X3 ◇ X3) ◇ (X1 ◇ X2)) := by
    intro X1 X0 X3 X2
    conv => enter [1, 2]; rw [l1 X0 X2 X3]
    conv => enter [1]; rw [l0 X1 X2 (X3 ◇ X3)]
  have l9 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X1 ◇ X1)) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l1 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (X1 ◇ X1)]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l9 sK0 X0 sK1 sK2 sK0]
  have l11 : ∀ X1 X0 X3 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X3 ◇ (X3 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X3 X2
    conv => enter [1]; rw [l8 X1 X0 X3 X2]
    conv => enter [1]; rw [← h4512 X3 X3 (X1 ◇ X2)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1 sK2 sK0]
  have l14 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l11 X1 X0 X1 X2]
    conv => enter [1]; rw [l5 X1 (X1 ◇ X2) sK0]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ sK0)]
  have l16 : ∀ X1 X0 sK0 X2 : G, (X1 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X1 X0 sK0 X2
    conv => enter [1]; rw [l14 X1 X0 X2 sK0]
    conv => enter [1]; rw [h43 (X1 ◇ X2) (sK0 ◇ sK0)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
  have l18 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l2 sK0 X1]
    conv => enter [1]; rw [l16 X1 X1 sK0 X2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
  have l20 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l12 sK0 X1]
    conv => enter [1]; rw [l18 X1 sK0 X2]
  have l21 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l21 sK0 X0 sK0 sK0]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l23 x y z]

theorem Equation43_4512_41637_implies_Equation41543 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41543 G := by
  have l0 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = ((sK3 ◇ sK0) ◇ X0) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4512 sK0 sK3 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK3]
  have l1 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = ((sK3 ◇ sK0) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [h43 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK0) sK2 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l5 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) = ((sK3 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l1 sK2 sK3 sK0 sK2]
    conv => enter [1, 2]; rw [l4 sK2 X0]
  have l6 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK3 sK3]
    conv => enter [1, 2]; rw [l4 sK3 X0]
  have l7 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) = ((sK3 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK3 sK0 sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK1]
  have l8 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) = ((sK1 ◇ sK1) ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l7 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) (sK1 ◇ sK1)]
  have l9 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ sK3) = (X0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [← l3 X0 sK0 sK3]
  have l10 : ∀ sK3 sK0 X0 sK2 X1 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (X1 ◇ X1)) := by
    intro sK3 sK0 X0 sK2 X1
    conv => enter [1, 2]; rw [l3 X0 sK2 X1]
    conv => enter [1]; rw [← l1 sK2 sK3 sK0 (X1 ◇ X1)]
  have l11 : ∀ sK0 X0 sK3 X1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK3 ◇ sK0) ◇ (X1 ◇ X1)) := by
    intro sK0 X0 sK3 X1
    conv => enter [1, 2]; rw [l3 X0 sK3 X1]
    conv => enter [1]; rw [l0 sK0 sK3 (X1 ◇ X1)]
  have l12 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l5 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [← l11 sK0 X0 sK3 sK2]
  have l13 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK3 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 2]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [← l10 sK3 sK0 X0 sK2 sK2]
  have l14 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK3 ◇ sK0) ◇ sK3) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l9 sK3 sK0 sK1]
  have l15 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ sK0) ◇ sK3) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l6 sK3 sK0 sK3]
    conv => enter [1]; rw [← l12 sK2 sK3 sK0 sK3]
  have l16 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK3 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l13 sK2 sK3 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK1]
  have l17 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ sK0) ◇ sK3) = ((sK1 ◇ sK1) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l15 sK3 sK0 sK3]
    conv => enter [1]; rw [l8 sK3 sK3 sK0 sK1]
  have l18 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l16 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) (sK1 ◇ sK1)]
  have l19 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l14 sK1 sK3 sK0]
    conv => enter [1]; rw [l17 sK3 sK0 sK1]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l18 sK2 sK3 sK0 sK1]
  have l21 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK3 sK0]
    conv => enter [1]; rw [← l20 sK1 sK2 sK3 sK0]
  have l22 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l22 x y z w]

theorem Equation4512_41637_implies_Equation41558 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41558 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_41637_implies_Equation41559 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41559 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l5 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l4 sK0 X2 X1]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation43_4512_41637_implies_Equation41562 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41562 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l6 : ∀ X0 sK2 sK1 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l5 X0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l0 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l7 sK0 sK2 sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l5 sK2 sK1]
    conv => enter [1]; rw [← l8 sK1 sK2 sK1]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK1 ◇ (sK2 ◇ sK2))]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2]
    conv => enter [1]; rw [l6 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2 sK1]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
    conv => enter [1]; rw [← l12 sK1 sK2]
  have l14 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l4 X0 sK0 sK0]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
  have l15 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l14 sK2 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [l15 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation43_4512_41637_implies_Equation41563 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41563 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l1 sK1 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l5 : ∀ sK1 X2 X1 : G, (sK1 ◇ sK1) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK1 X2 X1
    conv => enter [1]; rw [l4 sK1 X2 X1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0 sK1]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ sK0) sK2]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK1]
    conv => enter [1, 2]; rw [l7 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_41637_implies_Equation41632 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41632 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l2 sK1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1 sK1 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l4 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]
  conv => enter [1]; rw [l3 y]

theorem Equation43_4512_41637_implies_Equation41633 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41633 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l5 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l4 sK0 X2 X1]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation43_4512_41637_implies_Equation41636 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41636 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l3 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) (sK2 ◇ sK2)]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l4 sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
  have l8 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l9 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l12 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l5 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l14 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l0 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l12 sK0 sK2 sK1]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l11 sK2 sK1]
    conv => enter [1]; rw [← l14 sK1 sK2 sK1]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK1 ◇ (sK2 ◇ sK2))]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l17 sK1 sK2]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l11 sK2 sK1]
    conv => enter [1, 2]; rw [l18 sK1 sK1 sK2]
  have l20 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l10 X0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l21 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l20 X0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l21 sK2 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK2]
    conv => enter [1]; rw [l22 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l23 x y z]
  conv => enter [1]; rw [l19 y z]

theorem Equation43_4512_41637_implies_Equation41649 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41637 : Equation41637 G) : Equation41649 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41637 X1 X2 X2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41637 X0 X2 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41637 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41637 X0 X1 X1 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ sK1 X2 X1 : G, (sK1 ◇ sK1) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK1 X2 X1
    conv => enter [1]; rw [l3 sK1 X2 X1]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ (sK3 ◇ sK0)) sK2]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation43_4512_41636_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation308 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X2 X1 X1]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X2 X1 X1]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← l5 X2 X1 X1]
    conv => enter [1, 2]; rw [l3 X1 sK0]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← l4 X2 X1 X1]
    conv => enter [1, 2]; rw [l3 X1 sK0]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l3 X1 sK0]
  have l9 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l8 X1 X2 sK0]
    conv => enter [1]; rw [l6 X1 (X1 ◇ (X2 ◇ X2)) sK0]
  have l10 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l9 sK0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l10 sK0 X1 sK0]
  have l12 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0 X1]
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) X1 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation43_4512_41636_implies_Equation41530 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41530 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l2 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l1 X0 sK0]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l2 X1 X2 sK0]
    conv => enter [1]; rw [l3 X1 (X1 ◇ (X2 ◇ X2)) sK0]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 X1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation43_4512_41636_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41532 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1 X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l5 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l4 sK1 X1 X2]
  have l6 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l1 sK1 X1]
    conv => enter [1]; rw [l3 X1 X1 X2]
  have l7 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← l2 X2 X1 X1]
    conv => enter [1, 2]; rw [l1 X1 sK1]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41636 X0 (X1 ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [l1 (X1 ◇ X1) sK0]
  have l10 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [l0 (X1 ◇ X1) (X1 ◇ X1) (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ sK0) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [← l8 X1 X2 sK0]
    conv => enter [1]; rw [l7 X1 (X1 ◇ (X2 ◇ X2)) sK1]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l10 X0 sK0 X1]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X1) X1 X1]
  have l13 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l11 sK0 X1 X2 sK1]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK1 ◇ sK1)]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l12 X0 sK0 X1]
    conv => enter [1, 2]; rw [l0 X1 (X1 ◇ X1) X1]
  have l15 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l13 sK0 sK1 X1 sK0]
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1]
  have l16 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l14 X0 sK0 X0]
    conv => enter [1, 2]; rw [← l5 sK1 X0 X0]
  have l17 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l15 sK0 sK1 X1]
    conv => enter [1]; rw [← l6 X1 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l16 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l19 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l17 sK0 X1 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l20 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK0]
    conv => enter [1, 2]; rw [l21 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation43_4512_41636_implies_Equation41533 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41533 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1 X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l3 X1 X1 X2]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← l2 X2 X1 X1]
    conv => enter [1, 2]; rw [l1 X1 sK0]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l7 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l6 X1 X2 sK0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ (X2 ◇ X2)) sK0]
  have l8 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l7 sK0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 X1 sK0]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l9 sK0 X1]
    conv => enter [1]; rw [← l4 X1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l10 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation43_4512_41636_implies_Equation41539 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41539 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l3 X1 X1 X2]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK0]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l7 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l6 X1 X2 sK0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ (X2 ◇ X2)) sK0]
  have l8 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l7 sK0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 X1 sK0]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l9 sK0 X1]
    conv => enter [1]; rw [← l4 X1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation43_4512_41636_implies_Equation41543 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41543 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1 X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l1 sK1 X1]
    conv => enter [1]; rw [l3 X1 X1 X2]
  have l5 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← l2 X2 X1 X1]
    conv => enter [1, 2]; rw [l1 X1 sK1]
  have l6 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK1 ◇ sK1) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK1]
  have l7 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [← l6 X1 X2 sK1]
    conv => enter [1]; rw [l5 X1 (X1 ◇ (X2 ◇ X2)) sK1]
  have l8 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l7 sK1 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK1 ◇ sK1)]
  have l9 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l8 sK1 X1 sK1]
  have l10 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l9 sK1 X1]
    conv => enter [1]; rw [← l4 X1 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation43_4512_41636_implies_Equation41558 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41558 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1 X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [← l4 X1 sK1]
    conv => enter [1]; rw [l3 X1 X1 X2]
  have l7 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← l2 X2 X1 X1]
    conv => enter [1, 2]; rw [l4 X1 sK1]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ sK0) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [← l8 X1 X2 sK0]
    conv => enter [1]; rw [l7 X1 (X1 ◇ (X2 ◇ X2)) sK1]
  have l11 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l10 sK0 X1 X2 sK1]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l11 sK0 sK1 X1 sK0]
    conv => enter [1, 2, 2]; rw [l4 sK0 sK1]
  have l13 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l12 sK0 sK1 X1]
    conv => enter [1]; rw [← l6 X1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l14 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation43_4512_41636_implies_Equation41559 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41559 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l3 sK1 sK2]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41636 X0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK2 (sK1 ◇ sK2)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l9 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l7 X0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 sK2 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l10 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l9 X0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l10 X0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l12 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l11 X0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2))]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l8 X1 X0]
  have l14 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l8 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l15 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l8 sK0 X1]
    conv => enter [1]; rw [l14 X1 X1 X2]
  have l16 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l13 X1 X2 X1]
    conv => enter [1, 2]; rw [l8 X1 sK0]
  have l17 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l8 X1 sK0]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l5 sK1 sK2]
  have l19 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l17 X1 X2 sK0]
    conv => enter [1]; rw [l16 X1 (X1 ◇ (X2 ◇ X2)) sK0]
  have l20 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l19 sK0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l20 sK0 X1 sK0]
  have l22 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l21 sK0 X1]
    conv => enter [1]; rw [← l15 X1 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l24 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l18 sK0 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l24 sK1 sK2 sK0]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2))]
  have l27 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [l27 sK0 X0 sK1 sK2]
  have l29 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1, 1]; rw [l12 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X1]
  have l30 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l28 sK0 sK0 sK0 X1]
    conv => enter [1]; rw [← l29 X0 X1 sK0 sK0]
  have l31 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [l31 sK0 sK1 sK2]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK0]
    conv => enter [1, 2]; rw [l32 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l33 x y z]

theorem Equation43_4512_41636_implies_Equation41562 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41562 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1 X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ X1 sK2 X2 : G, (X1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK2 X2
    conv => enter [1, 2]; rw [l1 sK2 X1]
    conv => enter [1]; rw [l3 X1 X1 X2]
  have l5 : ∀ X1 X2 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [← l2 X2 X1 X1]
    conv => enter [1, 2]; rw [l1 X1 sK2]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l7 : ∀ sK0 X1 X2 sK2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 X1 X2 sK2
    conv => enter [1]; rw [← l6 X1 X2 sK0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ (X2 ◇ X2)) sK2]
  have l8 : ∀ sK0 sK2 X1 X2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [l7 sK0 X1 X2 sK2]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK2 ◇ sK2)]
  have l9 : ∀ sK0 sK2 X1 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l8 sK0 sK2 X1 sK0]
    conv => enter [1, 2, 2]; rw [l1 sK0 sK2]
  have l10 : ∀ sK0 X1 sK2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [l9 sK0 sK2 X1]
    conv => enter [1]; rw [← l4 X1 sK2 (sK2 ◇ sK2)]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l10 sK0 X1 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation43_4512_41636_implies_Equation41563 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41563 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l3 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK3 ◇ sK0)]
  have l4 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
  have l5 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l4 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK3 ◇ sK0)]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l7 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [h41636 X0 sK2 (sK3 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK2 sK3 sK0 (sK3 ◇ sK0)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l9 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l7 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [← l3 sK2 sK3 sK0 sK2 (sK2 ◇ (sK3 ◇ sK0))]
  have l10 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l9 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK3 ◇ sK0))]
  have l11 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l10 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK3 ◇ sK0))]
  have l12 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l11 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK3 ◇ sK0))]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l1 X1 X1 X2]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [l6 X2 X1 X1]
  have l15 : ∀ X1 X2 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← l14 X2 X1 X1]
    conv => enter [1, 2]; rw [l8 X1 sK1]
  have l16 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← l13 X2 X1 X1]
    conv => enter [1, 2]; rw [l8 X1 sK1]
  have l17 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK1 ◇ sK1) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l8 X1 sK1]
  have l18 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ sK1) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l8 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l5 sK2 sK3 sK0]
  have l19 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [← l17 X1 X2 sK1]
    conv => enter [1]; rw [l16 X1 (X1 ◇ (X2 ◇ X2)) sK1]
  have l20 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l19 sK1 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK1 ◇ sK1)]
  have l21 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l20 sK1 X1 sK1]
  have l22 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l21 sK1 X1]
    conv => enter [1]; rw [l15 (sK1 ◇ sK1) X1 sK1]
  have l23 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l1 sK2 (sK3 ◇ sK0) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l18 sK1 sK3 sK0 sK2]
  have l24 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [← l23 sK2 sK3 sK0 sK1]
  have l25 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK3 ◇ sK0))]
  have l26 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l25 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l1 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l27 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l22 sK1 X0]
    conv => enter [1]; rw [l26 X0 sK1 sK2 sK3 sK0]
  have l28 : ∀ X0 X1 sK2 sK3 sK0 : G, ((X0 ◇ X0) ◇ X1) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X1)) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1, 1]; rw [l12 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X1]
  have l29 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l27 sK1 sK1 sK1 sK1 X1]
    conv => enter [1]; rw [← l28 X0 X1 sK1 sK1 sK1]
  have l30 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l29 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK1]
    conv => enter [1, 2]; rw [l30 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l31 x y z w]

theorem Equation43_4512_41636_implies_Equation41632 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41632 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41636 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation43_4512_41636_implies_Equation41633 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41633 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [l3 sK1 sK2]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l5 sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l8 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41636 X0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l11 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l9 X0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l12 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l11 X0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l13 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l12 X0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l14 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l13 X0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l15 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l10 X1 X0]
  have l16 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l10 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l17 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l10 sK0 X1]
    conv => enter [1]; rw [l16 X1 X1 X2]
  have l18 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l15 X1 X2 X1]
    conv => enter [1, 2]; rw [l10 X1 sK0]
  have l19 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l10 X1 sK0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l21 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l19 X1 X2 sK0]
    conv => enter [1]; rw [l18 X1 (X1 ◇ (X2 ◇ X2)) sK0]
  have l22 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l21 sK0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK0 ◇ sK0)]
  have l23 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l22 sK0 X1 sK0]
  have l24 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l23 sK0 X1]
    conv => enter [1]; rw [← l17 X1 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l26 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [← l20 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l26 sK1 sK2 sK0]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l29 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l30 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [l29 sK0 X0 sK1 sK2]
  have l31 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1, 1]; rw [l14 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X1]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 sK0 sK0 X1]
    conv => enter [1]; rw [← l31 X0 X1 sK0 sK0]
  have l33 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l32 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l33 x y (y ◇ (y ◇ z))]

theorem Equation43_4512_41636_implies_Equation41637 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41636 : Equation41636 G) : Equation41637 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l3 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK3 ◇ sK0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK2 sK3 sK0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l4 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l3 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK3 ◇ sK0)]
  have l5 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK0]
  have l6 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK0) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l7 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK2 ◇ (sK3 ◇ sK0))]
  have l8 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [h41636 X0 sK2 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41636 X0 X0 X0]
    conv => enter [1]; rw [← h41636 X1 X0 X0]
  have l10 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l8 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK2 sK3 sK0 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l11 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l10 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l12 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l11 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l13 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l12 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l9 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1 X2]
  have l15 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l9 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l16 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l9 sK1 X1]
    conv => enter [1]; rw [l15 X1 X1 X2]
  have l17 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← l14 X2 X1 X1]
    conv => enter [1, 2]; rw [l9 X1 sK1]
  have l18 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK1 ◇ sK1) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← h41636 X1 X1 X2]
    conv => enter [1]; rw [l9 X1 sK1]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l6 sK2 sK3 sK0]
  have l20 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((X1 ◇ (X2 ◇ X2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [← l18 X1 X2 sK1]
    conv => enter [1]; rw [l17 X1 (X1 ◇ (X2 ◇ X2)) sK1]
  have l21 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l20 sK1 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ X2)) (sK1 ◇ sK1)]
  have l22 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l21 sK1 X1 sK1]
  have l23 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l22 sK1 X1]
    conv => enter [1]; rw [← l16 X1 sK1 (sK1 ◇ sK1)]
  have l24 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l23 sK1 X0]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
  have l25 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l19 sK1 sK2 sK3 sK0]
  have l26 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [← l25 sK2 sK3 sK0 sK1]
  have l27 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l26 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l28 : ∀ sK1 X0 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1, 1]; rw [l27 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
  have l29 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l24 sK1 X0]
    conv => enter [1]; rw [l28 sK1 X0 sK2 sK3 sK0]
  have l30 : ∀ X0 X1 sK2 sK3 sK0 : G, ((X0 ◇ X0) ◇ X1) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X1)) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1, 1]; rw [l13 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X1]
  have l31 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l29 sK1 sK1 sK1 sK1 X1]
    conv => enter [1]; rw [← l30 X0 X1 sK1 sK1 sK1]
  have l32 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l31 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l33 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l23 sK1 sK2]
    conv => enter [1, 2]; rw [l32 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l33 x y z w]

theorem Equation43_4512_41633_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation308 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X2 X1 X1]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 X1 X2]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l5 X1 X2 X1]
    conv => enter [1, 2]; rw [l3 X1 sK0]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← l4 X2 X1 X1]
    conv => enter [1, 2]; rw [l3 X1 sK0]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l3 X1 sK0]
  have l9 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l8 X1 X2 sK0]
    conv => enter [1]; rw [l6 X1 (X1 ◇ (X1 ◇ X2)) sK0]
  have l10 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l9 sK0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l10 sK0 sK0 X2]
    conv => enter [1, 2]; rw [l6 sK0 X2 sK0]
  have l12 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l11 sK0 X2]
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) X2 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation43_4512_41633_implies_Equation41530 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41530 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41633 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 sK0]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l3 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ sK0)]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l4 X0 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ sK1) sK0]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l5 X0 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK0)]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l6 X0 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l7 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l8 x x y]

theorem Equation43_4512_41633_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41532 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK1]
  have l5 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l1 sK1 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l7 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [← l6 X1 X2 sK0]
    conv => enter [1]; rw [l4 X1 (X1 ◇ (X1 ◇ X2)) sK1]
  have l8 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l7 sK0 X1 X2 sK1]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK1 ◇ sK1)]
  have l9 : ∀ sK0 sK1 X2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l8 sK0 sK1 sK0 X2]
    conv => enter [1, 2]; rw [l4 sK0 X2 sK1]
  have l10 : ∀ sK0 X2 sK1 : G, (sK0 ◇ sK0) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X2 sK1
    conv => enter [1]; rw [l9 sK0 sK1 X2]
    conv => enter [1]; rw [← l5 X2 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l10 sK0 X2 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation43_4512_41633_implies_Equation41533 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41533 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK0]
  have l5 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l7 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l6 X1 X2 sK0]
    conv => enter [1]; rw [l4 X1 (X1 ◇ (X1 ◇ X2)) sK0]
  have l8 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l7 sK0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 sK0 X2]
    conv => enter [1, 2]; rw [l4 sK0 X2 sK0]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l9 sK0 X2]
    conv => enter [1]; rw [← l5 X2 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l10 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation43_4512_41633_implies_Equation41539 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41539 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK0]
  have l5 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l1 sK0 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l7 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l6 X1 X2 sK0]
    conv => enter [1]; rw [l4 X1 (X1 ◇ (X1 ◇ X2)) sK0]
  have l8 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l7 sK0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 sK0 X2]
    conv => enter [1, 2]; rw [l4 sK0 X2 sK0]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l9 sK0 X2]
    conv => enter [1]; rw [← l5 X2 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation43_4512_41633_implies_Equation41543 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41543 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK1]
  have l5 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l1 sK1 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK1 ◇ sK1) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK1]
  have l7 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [← l6 X1 X2 sK1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ (X1 ◇ X2)) sK1]
  have l8 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l7 sK1 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK1 ◇ sK1)]
  have l9 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 sK1 X2]
    conv => enter [1, 2]; rw [l4 sK1 X2 sK1]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l9 sK1 X2]
    conv => enter [1]; rw [← l5 X2 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation43_4512_41633_implies_Equation41558 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41558 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l4 X1 sK1]
  have l7 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [← l4 X1 sK1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [← l8 X1 X2 sK0]
    conv => enter [1]; rw [l6 X1 (X1 ◇ (X1 ◇ X2)) sK1]
  have l11 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l10 sK0 X1 X2 sK1]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK0 sK1 X2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l11 sK0 sK1 sK0 X2]
    conv => enter [1, 2]; rw [l6 sK0 X2 sK1]
  have l13 : ∀ sK0 X2 sK1 : G, (sK0 ◇ sK0) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X2 sK1
    conv => enter [1]; rw [l12 sK0 sK1 X2]
    conv => enter [1]; rw [← l7 X2 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l14 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l13 sK0 X2 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation43_4512_41633_implies_Equation41559 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41559 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41633 X1 X2 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [← h41633 X0 X2 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l2 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l4 X1 X2 X1]
    conv => enter [1, 2]; rw [l2 X1 sK0]
  have l6 : ∀ X2 X1 sK0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X2 X1 sK0
    conv => enter [1]; rw [← l3 X1 X2 X2]
    conv => enter [1, 2]; rw [l2 X2 sK0]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l2 X1 sK0]
  have l8 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l7 X1 X2 sK0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ (X1 ◇ X2)) sK0]
  have l9 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l8 sK0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l9 sK0 sK0 X2]
    conv => enter [1, 2]; rw [l5 sK0 X2 sK0]
  have l11 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l10 sK0 X2]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) X2 sK0]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l13 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l12 sK0 X2 X1]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [l15 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation43_4512_41633_implies_Equation41562 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41562 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK2]
  have l5 : ∀ X1 sK2 X2 : G, (X1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK2 X2
    conv => enter [1, 2]; rw [l1 sK2 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l7 : ∀ sK0 X1 X2 sK2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 X1 X2 sK2
    conv => enter [1]; rw [← l6 X1 X2 sK0]
    conv => enter [1]; rw [l4 X1 (X1 ◇ (X1 ◇ X2)) sK2]
  have l8 : ∀ sK0 sK2 X1 X2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [l7 sK0 X1 X2 sK2]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK2 ◇ sK2)]
  have l9 : ∀ sK0 sK2 X2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X2
    conv => enter [1]; rw [l8 sK0 sK2 sK0 X2]
    conv => enter [1, 2]; rw [l4 sK0 X2 sK2]
  have l10 : ∀ sK0 X2 sK2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [l9 sK0 sK2 X2]
    conv => enter [1]; rw [← l5 X2 sK2 (sK2 ◇ sK2)]
  have l11 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l10 sK0 X2 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation43_4512_41633_implies_Equation41563 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41563 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l3 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
  have l4 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l3 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK3 ◇ sK0)]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X1 X2]
    conv => enter [1, 2]; rw [l6 X1 X0]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l5 X2 X1 X1]
  have l9 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ X0) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [l6 X0 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l4 sK2 sK3 sK0]
  have l10 : ∀ X1 X2 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← l8 X2 X1 X1]
    conv => enter [1, 2]; rw [l6 X1 sK1]
  have l11 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l7 X1 X2 X1]
    conv => enter [1, 2]; rw [l6 X1 sK1]
  have l12 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK1 ◇ sK1) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l6 X1 sK1]
  have l13 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ sK1) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l6 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l4 sK2 sK3 sK0]
  have l14 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [← l12 X1 X2 sK1]
    conv => enter [1]; rw [l11 X1 (X1 ◇ (X1 ◇ X2)) sK1]
  have l15 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l14 sK1 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK1 ◇ sK1)]
  have l16 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X2
    conv => enter [1]; rw [l15 sK1 sK1 X2]
    conv => enter [1, 2]; rw [l11 sK1 X2 sK1]
  have l17 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l16 sK1 X2]
    conv => enter [1]; rw [l10 (sK1 ◇ sK1) X2 sK1]
  have l18 : ∀ X0 sK1 sK3 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro X0 sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l13 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l1 (sK3 ◇ sK0) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l19 : ∀ sK1 sK3 sK0 sK2 X0 : G, (sK1 ◇ sK1) = ((sK3 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l17 sK1 X0]
    conv => enter [1]; rw [l18 X0 sK1 sK3 sK0 sK2]
  have l20 : ∀ X0 X1 sK3 sK0 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK3 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X1)) := by
    intro X0 X1 sK3 sK0 sK2
    conv => enter [1, 1]; rw [l9 X0 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK0) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X1]
  have l21 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l19 sK1 sK1 sK1 sK1 X1]
    conv => enter [1]; rw [← l20 X0 X1 sK1 sK1 sK1]
  have l22 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l21 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l17 sK1 sK1]
    conv => enter [1, 2]; rw [l22 sK1 sK2 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l23 x y z w]

theorem Equation43_4512_41633_implies_Equation41632 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41632 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l4 X1 sK1]
  have l6 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [← l4 X1 sK1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [← l7 X1 X2 sK0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ (X1 ◇ X2)) sK1]
  have l10 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l9 sK0 X1 X2 sK1]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l11 : ∀ sK0 sK1 X2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l10 sK0 sK1 sK0 X2]
    conv => enter [1, 2]; rw [l5 sK0 X2 sK1]
  have l12 : ∀ sK0 X2 sK1 : G, (sK0 ◇ sK0) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X2 sK1
    conv => enter [1]; rw [l11 sK0 sK1 X2]
    conv => enter [1]; rw [← l6 X2 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l13 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l12 sK0 X2 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation43_4512_41633_implies_Equation41636 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41633 : Equation41633 G) : Equation41636 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41633 X0 X0 X0]
    conv => enter [1]; rw [← h41633 X1 X0 X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [l0 X1 X2 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X2 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK2]
  have l5 : ∀ X1 sK2 X2 : G, (X1 ◇ (sK2 ◇ sK2)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK2 X2
    conv => enter [1, 2]; rw [l1 sK2 X1]
    conv => enter [1]; rw [l2 X1 X1 X2]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41633 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l7 : ∀ sK0 X1 X2 sK2 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 X1 X2 sK2
    conv => enter [1]; rw [← l6 X1 X2 sK0]
    conv => enter [1]; rw [l4 X1 (X1 ◇ (X1 ◇ X2)) sK2]
  have l8 : ∀ sK0 sK2 X1 X2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [l7 sK0 X1 X2 sK2]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X2)) (sK2 ◇ sK2)]
  have l9 : ∀ sK0 sK2 X2 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK2) ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X2
    conv => enter [1]; rw [l8 sK0 sK2 sK0 X2]
    conv => enter [1, 2]; rw [l4 sK0 X2 sK2]
  have l10 : ∀ sK0 X2 sK2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [l9 sK0 sK2 X2]
    conv => enter [1]; rw [← l5 X2 sK2 (sK2 ◇ sK2)]
  have l11 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l10 sK0 X2 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation43_4512_41632_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41632 : Equation41632 G) : Equation308 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41632 X0 X0]
    conv => enter [1]; rw [← h41632 X1 X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41632 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l3 X2 X0]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 X1 X2]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l6 X1 X2 X1]
    conv => enter [1, 2]; rw [l3 X1 sK0]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l5 X1 X2 X1]
    conv => enter [1, 2]; rw [l3 X1 sK0]
  have l9 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l4 X1 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [l3 X1 sK0]
  have l10 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = ((X2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l9 X1 X2 sK0]
    conv => enter [1]; rw [l7 X2 (X2 ◇ (sK0 ◇ sK0)) sK0]
  have l11 : ∀ X1 sK0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X2
    conv => enter [1]; rw [l10 X1 X2 sK0]
    conv => enter [1]; rw [h43 (X2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l12 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l11 X1 sK0 X2]
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) X2 sK0]
  have l13 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l12 sK0 X2 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation4512_41632_implies_Equation41530 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41632 : Equation41632 G) : Equation41530 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41632 X0 X0]
    conv => enter [1]; rw [← h41632 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h41632 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1]; rw [l2 X1 (X1 ◇ (X1 ◇ X1)) sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 X1]
    conv => enter [1, 2]; rw [l2 X1 X1 sK0]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 X1]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) X1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation43_4512_41632_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41632 : Equation41632 G) : Equation41532 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41632 X0 X0]
    conv => enter [1]; rw [← h41632 X1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l0 X1 X2 X2]
    conv => enter [1, 2]; rw [l1 X2 X0]
  have l4 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l1 sK1 X1]
    conv => enter [1]; rw [← l3 X2 X1 X1]
  have l5 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK1]
  have l6 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h41632 X1 X1]
    conv => enter [1]; rw [l1 X1 sK0]
  have l7 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = ((X1 ◇ (X1 ◇ X1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l6 X1 sK0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ (X1 ◇ X1)) sK1]
  have l8 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l7 sK0 X1 sK1]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X1)) (sK1 ◇ sK1)]
  have l9 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l8 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← l4 X1 sK1 X1]
  have l10 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l9 sK0 sK1 X1]
    conv => enter [1]; rw [← l4 X1 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l10 sK0 X1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation43_4512_41632_implies_Equation41533 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41632 : Equation41632 G) : Equation41533 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41632 X0 X0]
    conv => enter [1]; rw [← h41632 X1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41632 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l1 X2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l0 X1 X2 X2]
    conv => enter [1, 2]; rw [l1 X2 X0]
  have l5 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l1 sK0 X1]
    conv => enter [1]; rw [← l4 X2 X1 X1]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK0]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 sK0]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = ((X2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l7 X1 X2 sK0]
    conv => enter [1]; rw [l6 X2 (X2 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ X1 sK0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X2
    conv => enter [1]; rw [l8 X1 X2 sK0]
    conv => enter [1]; rw [h43 (X2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l10 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l9 X1 sK0 X2]
    conv => enter [1]; rw [← l5 X2 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l10 sK0 X2 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l11 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation43_4512_41632_implies_Equation41539 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41632 : Equation41632 G) : Equation41539 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41632 X0 X0]
    conv => enter [1]; rw [← h41632 X1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41632 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l1 X2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l0 X1 X2 X2]
    conv => enter [1, 2]; rw [l1 X2 X0]
  have l5 : ∀ X1 sK0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 X2
    conv => enter [1, 2]; rw [l1 sK0 X1]
    conv => enter [1]; rw [← l4 X2 X1 X1]
  have l6 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK0]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 sK0]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = ((X2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l7 X1 X2 sK0]
    conv => enter [1]; rw [l6 X2 (X2 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ X1 sK0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X2
    conv => enter [1]; rw [l8 X1 X2 sK0]
    conv => enter [1]; rw [h43 (X2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l10 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l9 X1 sK0 X2]
    conv => enter [1]; rw [← l5 X2 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l10 sK0 X2 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation43_4512_41632_implies_Equation41543 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41632 : Equation41632 G) : Equation41543 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41632 X0 X0]
    conv => enter [1]; rw [← h41632 X1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41632 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l1 X2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l0 X1 X2 X2]
    conv => enter [1, 2]; rw [l1 X2 X0]
  have l5 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [l1 sK1 X1]
    conv => enter [1]; rw [← l4 X2 X1 X1]
  have l6 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l1 X1 sK1]
  have l7 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 sK1]
  have l8 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = ((X2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l7 X1 X2 sK1]
    conv => enter [1]; rw [l6 X2 (X2 ◇ (sK1 ◇ sK1)) sK1]
  have l9 : ∀ X1 sK1 X2 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1 X2
    conv => enter [1]; rw [l8 X1 X2 sK1]
    conv => enter [1]; rw [h43 (X2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l10 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l9 X1 sK1 X2]
    conv => enter [1]; rw [← l5 X2 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l10 sK1 X2 sK1]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w]

theorem Equation43_4512_41632_implies_Equation41558 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41632 : Equation41632 G) : Equation41558 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41632 X0 X0]
    conv => enter [1]; rw [← h41632 X1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41632 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l1 X2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X1 X2]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l0 X1 X2 X2]
    conv => enter [1, 2]; rw [l1 X2 X0]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ X1 sK1 X2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK1 X2
    conv => enter [1, 2]; rw [← l5 X1 sK1]
    conv => enter [1]; rw [← l4 X2 X1 X1]
  have l7 : ∀ X1 X2 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l3 X1 X2 X1]
    conv => enter [1, 2]; rw [l5 X1 sK1]
  have l8 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [l5 X1 sK1]
  have l9 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = ((X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l8 X1 X2 sK1]
    conv => enter [1]; rw [l7 X2 (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) sK1]
  have l10 : ∀ X1 sK1 X2 : G, (X1 ◇ X1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X1 sK1 X2
    conv => enter [1]; rw [l9 X1 X2 sK1]
    conv => enter [1]; rw [h43 (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l11 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l10 X1 sK1 X2]
    conv => enter [1]; rw [← l6 X2 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK1 X2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X2
    conv => enter [1]; rw [← l5 sK1 sK1]
    conv => enter [1]; rw [l11 sK1 X2 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

end CommutativeSemigroup5
