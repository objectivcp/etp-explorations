import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41667_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41667 : Equation41667 G) : Equation41557 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h41667 X0 X1 X2 X3]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41667 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ X0)))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X0 X0 X0]
  have l3 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l0 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l4 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l3 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ X0)) X4]
  have l5 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X3 ◇ X0) X4]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X0 X4]
  have l7 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 X0 X2 X1 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X1 X1 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [← l9 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]
  conv => enter [1]; rw [l8 y x y]
  conv => enter [1]; rw [l8 y (y ◇ x) x]

theorem Equation4512_41667_implies_Equation41628 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41667 : Equation41667 G) : Equation41628 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41667 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41667 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ X0)))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X0 X0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l3 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation4512_41667_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41667 : Equation41667 G) : Equation41534 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41667 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0 X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK1 sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41667 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h41667 (sK1 ◇ (sK0 ◇ sK0)) X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l7 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41667 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ X0)))]
  have l8 : ∀ sK1 X0 sK0 X1 X2 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))) := by
    intro sK1 X0 sK0 X1 X2
    conv => enter [1, 2]; rw [h41667 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X1 X2]
    conv => enter [1]; rw [l3 sK1 sK0 (X1 ◇ (X0 ◇ (X2 ◇ X0)))]
  have l9 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l8 sK1 X0 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h41667 X0 (sK1 ◇ (sK0 ◇ sK0)) sK1 sK1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X0 X0 X0]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l6 sK1 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h41667 (sK0 ◇ sK0) X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l10 (sK0 ◇ sK0) sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 (sK1 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 sK1]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) sK0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l15 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l18 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [← l20 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l23 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK1]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h41667 sK0 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41667 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l28 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l29 x y]
  conv => enter [1]; rw [l27 y x]

theorem Equation4512_41667_implies_Equation53938 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41667 : Equation41667 G) : Equation53938 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h41667 X0 X1 X2 X3]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41667 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ X0)))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X0 X0 X0]
  have l3 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l0 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l4 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l3 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ X0)) X4]
  have l5 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X3 ◇ X0) X4]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X0 X4]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h41667 X0 X2 X1 X1]
    conv => enter [1]; rw [← l6 X1 X0 X2 X2 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l7 X1 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1]; rw [l2 y z]
  conv => enter [1, 2]; rw [l2 y x]

theorem Equation4512_41667_implies_Equation53959 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41667 : Equation41667 G) : Equation53959 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41667 (X1 ◇ X0) X2 X1 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X1 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h41667 X0 X1 X2 X3]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41667 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ X0)))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X0 X0 X0]
  have l4 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l1 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l4 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ X0)) X4]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X1]
  have l8 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X3 ◇ X0) X4]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X0 X4]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h41667 X0 X2 X1 X1]
    conv => enter [1]; rw [← l9 X1 X0 X2 X2 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X1]
    conv => enter [1]; rw [l10 X1 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l11 y x]
  conv => enter [1]; rw [l7 y z]

theorem Equation4512_41667_implies_Equation54270 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41667 : Equation41667 G) : Equation54270 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h41667 X2 X3 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h41667 X0 X1 X2 X3]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41667 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ X0)))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X0 X0 X0]
  have l4 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X0))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l1 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l5 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l4 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ X0)) X4]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X3 ◇ X0) X4]
  have l7 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X0 X4]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h41667 X0 X2 X1 X1]
    conv => enter [1]; rw [← l7 X1 X0 X2 X2 X0]
  have l9 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [l0 X0 X3 X1 X1 X2]
    conv => enter [1]; rw [← l7 X1 (X2 ◇ X0) X3 X3 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X1]
    conv => enter [1]; rw [l8 X1 X1 X0]
  intro x y z
  conv => enter [1]; rw [l9 x y z x]

theorem Equation4512_41667_implies_Equation54261 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41667 : Equation41667 G) : Equation54261 G := by
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
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l6 : ∀ sK1 sK0 X0 X1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X0 X1 sK2
    conv => enter [1]; rw [h41667 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0 X1 sK2]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK2 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41667 (sK0 ◇ sK1) X0 X1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [l3 sK0 sK1]
  have l8 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41667 (X1 ◇ X0) X2 X1 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X1 (X1 ◇ X0) X1]
  have l9 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h41667 (sK0 ◇ sK1) X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l4 sK1 sK0 (X0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41667 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ X0)))]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41667 X0 X0 X0 X0]
  have l12 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l9 sK0 sK1 X1 X0]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l8 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l14 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK1 sK0 X0 X1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0 X0 X1 sK2
    conv => enter [1]; rw [l6 sK1 sK0 X0 X1 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X0]
    conv => enter [1]; rw [l13 X0 X0 X1]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l11 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0]
  have l18 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK0 X0 sK1 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1 sK0]
    conv => enter [1]; rw [← l11 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l18 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 (sK1 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l20 X0 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41667 sK1 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h41667 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK0]
  have l25 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [← l24 sK0 sK1]
    conv => enter [1]; rw [← l22 sK1 sK0 sK2]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l23 sK1 sK1]
    conv => enter [1]; rw [← l25 sK2 sK1 sK1]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l26 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l27 z y x]

theorem Equation4512_41667_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41667 : Equation41667 G) : Equation41529 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [l7 sK0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41667 (sK0 ◇ sK0) X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41667 sK0 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41667 (sK0 ◇ sK0) X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41667 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l16 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1, 2]; rw [← l18 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0 sK0]
    conv => enter [1, 2]; rw [l18 sK0]
  intro x
  conv => enter [1]; rw [l21 x]

@[equational_result]
theorem Equation41553_implies_Equation41551 (G : Type*) [Magma G] (h41553 : Equation41553 G) : Equation41551 G := by
  intro x y z
  conv => enter [1]; rw [h41553 x y z y]

theorem Equation4512_41553_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41553 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l3 : ∀ sK1 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X1 ◇ X2))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41553 sK1 X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ (X1 ◇ X2)))]
  have l4 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X1 ◇ X2))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l2 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK1) sK1 sK1 sK1]
    conv => enter [1]; rw [← l4 sK1 sK1 sK1 sK1]
  have l7 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l5 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l9 X0 X4 X0 X0 X0]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l10 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1]; rw [← l11 (sK1 ◇ sK1) X0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [← l13 sK1 X0]
  have l15 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41553 X0 (sK1 ◇ sK1) X0 X0]
    conv => enter [1, 2]; rw [← l14 sK1 (X0 ◇ (X0 ◇ X0))]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation4512_41553_implies_Equation41548 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation41548 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41553 X1 X0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41553 X0 X1 X1 X1]
  have l2 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41553 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l4 : ∀ sK1 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X1 ◇ X2))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41553 sK1 X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ (X1 ◇ X2)))]
  have l5 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X1 ◇ X2))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l3 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK1) sK1 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK1 sK1 sK1]
  have l8 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l6 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l10 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l11 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l10 X0 X4 X0 X0 X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l11 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l14 sK1 X0]
    conv => enter [1]; rw [← l12 (sK1 ◇ sK1) X0]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1]; rw [← l15 sK1 X0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l18 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41553 X0 (sK1 ◇ sK1) X0 X0]
    conv => enter [1, 2]; rw [← l16 sK1 (X0 ◇ (X0 ◇ X0))]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ X0)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l18 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l26 x y]

@[equational_result]
theorem Equation41553_implies_Equation41550 (G : Type*) [Magma G] (h41553 : Equation41553 G) : Equation41550 G := by
  intro x y z
  conv => enter [1]; rw [h41553 x y z x]

theorem Equation4512_41553_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation41547 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41553 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_41553_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation41557 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41553 X1 X0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41553 X0 X1 X1 X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l4 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l5 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l4 X0 X4 X0 X0 X0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK0)]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l0 X0 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_41553_implies_Equation41538 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation41538 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l6 sK1]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41553 X1 X0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41553 X0 X1 X1 X1]
  have l10 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41553 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l11 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41553 (sK1 ◇ sK1) (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l4 sK1 ((sK1 ◇ sK1) ◇ (X0 ◇ X1))]
  have l12 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l13 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X2))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41553 sK0 X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X1 ◇ X2)))]
  have l14 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41553 sK1 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (X0 ◇ X1))]
  have l15 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l14 sK1 X0 X1]
    conv => enter [1]; rw [← l2 sK1 (X0 ◇ X1)]
  have l16 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X2))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X0 X1 X2]
  have l17 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l12 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l18 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l11 sK1 X0 X1]
    conv => enter [1, 2]; rw [l8 sK1 (X0 ◇ X1)]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0) sK0 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0 sK0 sK0]
  have l20 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l17 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l21 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l18 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l23 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l20 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l21 sK1 sK1 sK1]
  have l25 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l26 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l23 X0 X4 X0 X0 X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← l26 (sK0 ◇ sK0) X0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l28 sK0 X0]
  have l30 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l24 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l31 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l32 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l31 sK1]
    conv => enter [1]; rw [← l30 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l32 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l33 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l34 x y]

theorem Equation4512_41553_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation41534 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41553 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l3 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X2))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41553 sK0 X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X1 ◇ X2)))]
  have l4 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X2))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l2 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0 sK0 sK0]
  have l7 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l5 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l9 X0 X4 X0 X0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l11 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation4512_41553_implies_Equation53877 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation53877 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41553 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l3 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (X1 ◇ X2))))) := by
    intro sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41553 sK2 X0 X1 X2]
    conv => enter [1]; rw [l0 sK2 (X0 ◇ (sK2 ◇ (X1 ◇ X2)))]
  have l4 : ∀ sK2 X0 X1 X2 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (X1 ◇ X2))))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [← l0 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l2 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l6 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l1 sK2 (sK2 ◇ sK2) sK2 sK2 sK2]
    conv => enter [1]; rw [← l4 sK2 sK2 sK2 sK2]
  have l7 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l5 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l8 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l6 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l10 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l8 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l11 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l9 X0 X4 X0 X0 X0]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l10 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l10 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l14 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l13 sK2 X0]
    conv => enter [1]; rw [← l11 (sK2 ◇ sK2) X0]
  have l15 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l10 sK2]
    conv => enter [1]; rw [← l14 sK2 X0]
  have l16 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
  have l17 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l15 sK2 X0]
  have l18 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [← l17 sK1 sK2 X0]
  have l19 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41553 X0 (sK1 ◇ (sK2 ◇ sK2)) X0 X0]
    conv => enter [1, 2]; rw [← l18 sK1 sK2 (X0 ◇ (X0 ◇ X0))]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

theorem Equation4512_41553_implies_Equation53881 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation53881 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK2) X0]
  have l1 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK2 sK0]
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ X0)) = (((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK0 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l3 sK0 sK2]
  have l5 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41553 X1 X0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41553 X0 X1 X1 X1]
  have l7 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41553 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l8 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l9 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (X1 ◇ X2))))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41553 (sK0 ◇ sK2) X0 X1 X2]
    conv => enter [1]; rw [l5 sK0 sK2 (X0 ◇ ((sK0 ◇ sK2) ◇ (X1 ◇ X2)))]
  have l10 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (X1 ◇ X2))))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [← l5 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l9 sK0 sK2 X0 X1 X2]
  have l11 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l8 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l12 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 (sK0 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK0 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK2 sK0 sK0 sK0]
  have l13 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l11 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l14 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l12 sK0 sK2]
    conv => enter [1, 2]; rw [l3 sK0 sK2]
  have l15 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l13 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l16 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 sK2]
    conv => enter [1]; rw [← l0 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l17 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l15 X0 X4 X0 X0 X0]
  have l18 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l16 sK0 sK2]
  have l19 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l18 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0]
  have l20 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK2 X0]
    conv => enter [1]; rw [← l17 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0]
  have l21 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK2]
    conv => enter [1]; rw [← l20 sK0 sK2 X0]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l6 sK0 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK0 ◇ sK2))]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK2 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l22 sK0 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l17 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

theorem Equation4512_41553_implies_Equation54166 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation54166 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41553 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l3 : ∀ sK1 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X1 ◇ X2))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41553 sK1 X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ (X1 ◇ X2)))]
  have l4 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X1 ◇ X2))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l2 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK1) sK1 sK1 sK1]
    conv => enter [1]; rw [← l4 sK1 sK1 sK1 sK1]
  have l7 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l5 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l9 X0 X4 X0 X0 X0]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l10 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1]; rw [← l11 (sK1 ◇ sK1) X0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [← l13 sK1 X0]
  have l15 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41553 X0 (sK1 ◇ sK1) X0 X0]
    conv => enter [1, 2]; rw [← l14 sK1 (X0 ◇ (X0 ◇ X0))]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l11 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l15 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l16 x y z]

theorem Equation4512_41553_implies_Equation54183 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation54183 G := by
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
  have l6 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41553 X1 X0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41553 X0 X1 X1 X1]
  have l8 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41553 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l9 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l10 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (X1 ◇ X2))))) := by
    intro sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41553 sK2 X0 X1 X2]
    conv => enter [1]; rw [l6 sK2 (X0 ◇ (sK2 ◇ (X1 ◇ X2)))]
  have l11 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41553 (sK0 ◇ sK1) X0 X1 X2]
    conv => enter [1]; rw [l5 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ X2)))]
  have l12 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l11 sK0 sK1 X0 X1 X2]
  have l13 : ∀ sK2 X0 X1 X2 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (X1 ◇ X2))))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [← l6 sK2 sK2]
    conv => enter [1]; rw [l10 sK2 X0 X1 X2]
  have l14 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l9 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 sK0 sK0 sK0]
  have l16 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l8 sK2 (sK2 ◇ sK2) sK2 sK2 sK2]
    conv => enter [1]; rw [← l13 sK2 sK2 sK2 sK2]
  have l17 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l14 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l19 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l16 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l20 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l17 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l22 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l19 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l23 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l20 X0 X4 X0 X0 X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l25 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l22 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l26 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l25 sK2 X0]
    conv => enter [1]; rw [← l23 (sK2 ◇ sK2) X0]
  have l27 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l22 sK2]
    conv => enter [1]; rw [← l26 sK2 X0]
  have l28 : ∀ X0 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h41553 X0 (sK2 ◇ sK2) X0 X0]
    conv => enter [1, 2]; rw [← l27 sK2 (X0 ◇ (X0 ◇ X0))]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0]
    conv => enter [1]; rw [← l23 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l31 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1 X0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l34 sK0 sK1 X0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l36 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l28 sK0 sK2]
    conv => enter [1]; rw [← l35 sK0 sK1 X0]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK0]
    conv => enter [1]; rw [← l36 sK0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l37 x z y]

theorem Equation4512_41553_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41553 : Equation41553 G) : Equation41529 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [l8 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0) X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l9 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41553 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l4 sK0 (X0 ◇ X1)]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41553 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 X1]
    conv => enter [1, 2]; rw [← l10 sK0 (X0 ◇ X1)]
  have l17 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41553 X0 X1 X2 X3]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41553 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1))]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41553 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0 X1]
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1]
    conv => enter [1]; rw [← l14 sK0 (X0 ◇ X1)]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l18 sK0 X0 X1]
    conv => enter [1]; rw [← l12 sK0 (X0 ◇ X1)]
  have l22 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l17 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0 X0 X1]
  have l24 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l20 sK0 X0 X1]
  have l25 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0 X0 X1]
  have l26 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l22 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 sK0 sK0]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0 sK0 sK0]
    conv => enter [1]; rw [← l24 sK0 sK0 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 sK0 sK0]
    conv => enter [1]; rw [← l25 sK0 sK0 sK0]
  have l30 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l26 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l31 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41553 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l30 X0 X4 X0 X0 X0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l27 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [← l31 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l3 sK0]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l34 sK0 X0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1, 1]; rw [← l29 sK0]
  have l37 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x
  conv => enter [1]; rw [l37 x]

theorem Equation4512_41661_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation316 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l5 sK1]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l8 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41661 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l8 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l11 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l10 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l12 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l11 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l13 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l12 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l14 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l15 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l9 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l9 (X0 ◇ X1) sK1]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1)]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l15 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l18 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l13 (sK1 ◇ sK1) (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l17 sK1 X0 X1]
  have l20 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l19 sK1 X0 X1]
  have l21 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [← l5 sK1]
    conv => enter [1]; rw [l20 sK1 X0 X1]
  have l22 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l21 sK1 X0 X1]
  have l23 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l18 sK1]
    conv => enter [1]; rw [l22 sK1 X0 X1]
  have l24 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41661 X0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l16 sK1]
  have l25 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l24 X0 sK1]
    conv => enter [1]; rw [l7 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l25 X0 sK1]
    conv => enter [1]; rw [← l23 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l27 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l28 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l29 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [l26 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l30 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1, 2]; rw [l26 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l31 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l30 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [← l31 sK1]
  have l33 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l32 sK1]
    conv => enter [1]; rw [l26 (sK1 ◇ sK1) sK1]
  have l34 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l33 sK1]
    conv => enter [1]; rw [← l29 sK1]
  have l35 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l26 X0 sK1]
    conv => enter [1]; rw [← l33 sK1]
  intro x y
  conv => enter [1]; rw [l35 x y]
  conv => enter [1]; rw [l34 y]

theorem Equation4512_41661_implies_Equation41565 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41565 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41661 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41661 X0 X1 X2]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41661 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h41661 X0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK1)) (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h41661 X0 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l3 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l7 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l8 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l11 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l9 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l12 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l11 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 (sK0 ◇ sK1) sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1 sK0]
  have l18 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) sK0 sK1]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l4 (X0 ◇ X1) sK0 sK1]
  have l19 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l4 sK2 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 (sK0 ◇ sK1) (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l19 sK0 sK1 X0 X1]
  have l22 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1 X0 X1]
  have l23 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1 X0 X1]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 sK0]
  have l25 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ (X1 ◇ X1)) sK0 sK1]
    conv => enter [1]; rw [l10 (X0 ◇ (X1 ◇ X1)) X0 X1]
    conv => enter [1, 2, 2]; rw [l4 (X0 ◇ (X1 ◇ X1)) sK0 sK1]
  have l26 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l25 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) (sK0 ◇ sK1)]
  have l27 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l24 X0 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))]
  have l28 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0 sK0 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l26 sK0 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l23 sK0 sK0 X0 (X1 ◇ X1)]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l27 X0 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l30 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l29 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l28 sK0 X0 sK0]
  have l31 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l30 X0 sK0]
    conv => enter [1]; rw [← l28 sK0 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l31 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l31 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK0]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [l31 sK2 sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l33 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

theorem Equation4512_41661_implies_Equation41585 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41585 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41661 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41661 X0 X1 X2]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41661 sK1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l4 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41661 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l4 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l7 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l8 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l11 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l9 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l12 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l11 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41661 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2, 2]; rw [← l6 X0 sK1 sK0]
  have l14 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l5 (X0 ◇ X1) sK1]
  have l15 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l14 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l12 (sK1 ◇ sK1) (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l16 sK1 X0 X1]
  have l18 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l5 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l17 sK1 X0 X1]
  have l19 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l15 sK1]
    conv => enter [1]; rw [l1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK1]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK1 ◇ sK1)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l23 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41661 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l20 sK1]
  have l24 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l23 X0 sK1]
    conv => enter [1]; rw [← l18 sK1 (sK1 ◇ sK1) X0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l26 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l24 X0 sK1]
    conv => enter [1]; rw [← l20 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l22 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l26 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l30 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l10 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ X0)]
  have l31 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l10 X0 (X1 ◇ X1) X1]
  have l32 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l31 X1 X0]
    conv => enter [1, 2]; rw [l26 X0 sK1]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK1 sK0 sK1]
  have l34 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l32 X1 X0 X1]
    conv => enter [1, 2]; rw [l29 X1 sK0]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1, 2]; rw [l26 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
  have l36 : ∀ sK1 X0 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l34 sK1 X0 sK0]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l37 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1, 2]; rw [l39 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l40 x y]

theorem Equation4512_41661_implies_Equation41605 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41605 G := by
  have l0 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l1 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) = (((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l1 sK2 sK1 sK0]
  have l3 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l2 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h41661 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1, 2, 2]; rw [l3 sK2 sK1 sK0 X0]
  have l5 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ X0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l7 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h41661 X0 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))]
  have l8 : ∀ sK1 sK0 X0 sK2 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X1 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X1)))) := by
    intro sK1 sK0 X0 sK2 X1
    conv => enter [1, 2]; rw [h41661 X0 (sK2 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2 (X1 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X1)))]
  have l9 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l10 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l9 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l11 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK1 sK0 sK2]
    conv => enter [1]; rw [← l8 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK2 sK2]
  have l12 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l10 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l13 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK1 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2 (sK2 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l12 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l15 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l14 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l16 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ X0)) = (((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 sK2 X0]
    conv => enter [1, 1]; rw [l13 sK2 sK1 sK0]
  have l17 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [l16 sK2 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l18 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1) sK1 sK0 sK2]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l7 (X0 ◇ X1) sK1 sK0 sK2]
  have l19 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))))))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [l18 sK1 sK0 sK2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
  have l20 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l15 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [← l19 sK1 sK0 sK2 X0 X1]
  have l21 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l7 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) sK1 sK0 sK2]
    conv => enter [1]; rw [l20 sK1 sK0 sK2 X0 X1]
  have l22 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  have l23 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l22 sK1 sK0 sK2]
  have l24 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l5 (sK1 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [← l23 sK1 sK0 sK2]
  have l25 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l5 sK2 sK1 sK0]
  have l26 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ X0) = (sK2 ◇ (sK2 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK2 sK2]
    conv => enter [1, 2, 2, 2]; rw [← l25 sK1 sK0 sK2]
  have l27 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l26 X0 sK2 sK1 sK0]
    conv => enter [1]; rw [l17 sK2 (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) sK1 sK0]
  have l28 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l27 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l21 sK1 sK0 sK2 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l29 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X0 X0 X0]
    conv => enter [1]; rw [← l28 X1 X0 X0 X0]
  have l30 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [l28 sK2 sK1 sK0 sK2]
  have l31 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l28 X0 sK1 sK0 X0]
    conv => enter [1]; rw [← l24 sK1 sK0 X0]
  have l32 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l30 sK1 sK0 sK2]
    conv => enter [1]; rw [l31 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) sK1 sK0]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l32 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l33 x y z]

theorem Equation4512_41661_implies_Equation41592 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41592 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41661 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41661 X0 X1 X2]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41661 (sK0 ◇ sK1) X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l9 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41661 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l7 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l12 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l9 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
    conv => enter [1]; rw [← l20 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation4512_41661_implies_Equation41548 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41548 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41661 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41661 X0 X1 X2]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41661 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l2 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l4 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l10 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l3 (X0 ◇ X1) sK1]
  have l11 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l12 sK1 X0 X1]
  have l14 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l3 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l13 sK1 X0 X1]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l7 X0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))]
  have l17 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l16 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 sK1]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l14 sK1 X0 (sK1 ◇ sK1)]
  have l19 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l17 X0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l18 sK1 X0]
    conv => enter [1, 2]; rw [← l11 sK1]
  have l21 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l19 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l22 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l21 X0 sK1]
    conv => enter [1, 2]; rw [← l14 sK1 X0 (sK1 ◇ sK1)]
  have l23 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l22 X0 sK1]
    conv => enter [1]; rw [← l11 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [← l20 sK1 sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK1]
    conv => enter [1, 2]; rw [l20 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l23 (sK1 ◇ sK1) sK1]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2]; rw [l25 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l27 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l28 x y]

theorem Equation4512_41661_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41621 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41661 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41661 X0 X1 X2]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l8 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l9 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l8 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
  have l11 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l9 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l10 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l13 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l11 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l14 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l13 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l15 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1) sK1 sK0]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l7 (X0 ◇ X1) sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 (sK1 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l18 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l15 sK1 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l19 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l14 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1]; rw [← l18 sK1 sK0 X0 X1]
  have l20 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l7 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0 X0 X1]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 (sK1 ◇ sK0) X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l4 sK1 sK0 (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l22 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l12 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l4 sK1 sK0 (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))]
  have l23 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l22 X0 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l4 sK1 sK0 (sK1 ◇ sK0)]
  have l24 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l21 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l20 sK1 sK0 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l25 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l23 X0 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l6 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK0]
  have l26 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
  have l27 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l25 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l20 sK1 sK0 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l28 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l26 sK1 sK0 X0]
  have l29 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l27 X0 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l29 x y x]
  conv => enter [1]; rw [l28 y x y]

theorem Equation4512_41661_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41547 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41661 (sK1 ◇ sK0) sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41661 X0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l8 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l7 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK0]
  have l10 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l8 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0)]
  have l12 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l10 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l14 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l12 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41661 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0]
    conv => enter [1, 2, 2]; rw [← l13 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0)]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41661 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l6 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0 sK1]
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l5 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK1 sK0]
  have l22 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) sK1 sK0]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l5 (X0 ◇ X1) sK1 sK0]
  have l23 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l22 sK1 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l25 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l14 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1]; rw [← l23 sK1 sK0 X0 X1]
  have l26 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l5 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK0]
    conv => enter [1]; rw [l25 sK1 sK0 X0 X1]
  have l27 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [l26 sK1 sK0 X0 X1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l30 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK1 sK0]
  have l31 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l30 X0 sK1 sK0]
    conv => enter [1]; rw [← l27 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l31 (sK0 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [l31 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l32 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l34 x y]

theorem Equation4512_41661_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41557 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41661 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41661 X0 X1 X2]
  have l6 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41661 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41661 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l11 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41661 X0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))]
  have l12 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l13 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l12 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l14 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
  have l15 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l13 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l16 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l14 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l17 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l15 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l18 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l17 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41661 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2, 2]; rw [← l11 X0 sK0 sK1]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 sK1]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 sK0]
  have l21 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41661 (sK1 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l9 X0 sK1 sK0]
  have l23 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1) sK1 sK0]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l8 (X0 ◇ X1) sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 (sK1 ◇ sK0)]
  have l25 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l23 sK1 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l26 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l18 (sK1 ◇ sK0) (sK1 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l25 sK1 sK0 X0 X1]
  have l27 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l8 (sK1 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [l26 sK1 sK0 X0 X1]
  have l28 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l8 sK1 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l29 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l28 sK1 X0 sK0]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41661 sK1 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l24 sK0 sK1]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [← l7 (sK1 ◇ sK0) sK0]
  have l32 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK0)))))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l16 X1 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2, 2]; rw [l8 (X0 ◇ X0) sK1 sK0]
  have l33 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 sK1 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ sK0) (X0 ◇ X0)]
  have l34 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (X0 ◇ X0)]
  have l35 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ (X1 ◇ X1)) sK1 sK0]
    conv => enter [1]; rw [l16 (X0 ◇ (X1 ◇ X1)) X0 X1]
    conv => enter [1, 2, 2]; rw [l8 (X0 ◇ (X1 ◇ X1)) sK1 sK0]
  have l36 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l16 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l37 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l36 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l31 sK1 sK0]
  have l38 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X1) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l35 sK1 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) (sK1 ◇ sK0)]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK0 sK1 sK0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l22 sK1 sK0 sK1]
  have l41 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK0))))))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l32 X1 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK0)))))]
  have l42 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0 sK0 sK0]
    conv => enter [1]; rw [← l16 (sK0 ◇ sK0) sK0 sK0]
  have l43 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l27 sK1 sK0 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l38 sK1 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l27 sK1 sK0 X0 (X1 ◇ X1)]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [← l29 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l46 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))))))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l41 X1 X0 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X0 (sK1 ◇ sK0)]
  have l47 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l31 sK1 sK1]
    conv => enter [1]; rw [l43 sK1 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l31 sK1 sK1]
  have l48 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l46 X1 X0 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l27 sK1 sK0 X0 X0]
  have l49 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1))))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l48 X1 X0 sK1 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l31 sK1 X1]
  have l50 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [l49 X1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l47 sK1 X0 X1]
  have l51 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l50 X1 X1 sK1]
    conv => enter [1]; rw [← l47 sK1 X1 X1]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [← l44 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l52 sK0 sK1]
  have l54 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l42 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l51 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l57 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l58 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK1 sK0]
    conv => enter [1, 2]; rw [← l45 sK1 sK0]
  have l59 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l60 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l59 sK1 X0 sK0]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [l58 sK1 sK0]
    conv => enter [1, 2]; rw [l56 sK1 sK0]
  have l62 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l57 sK0 X0 sK1]
    conv => enter [1]; rw [l60 sK1 X0 sK0]
  have l63 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0 (sK0 ◇ sK0)]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK0)]
  have l65 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l53 sK0 sK0]
    conv => enter [1]; rw [← l64 sK0 sK0]
  have l66 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l63 sK1 sK0]
    conv => enter [1, 2]; rw [← l20 sK1 sK0]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1]; rw [← l66 sK1 sK0]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l67 sK0 sK1]
  have l69 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h41661 X0 X1 X1]
    conv => enter [1, 2, 2, 2]; rw [l51 X1 sK1]
  have l70 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l56 X0 sK0]
  have l71 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l69 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l47 sK1 X1 X0]
  have l72 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l71 X0 X1 X0]
    conv => enter [1, 2]; rw [l56 X0 sK0]
  have l73 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l72 sK0 X1 sK0]
  have l74 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l73 sK0 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ sK0)]
  have l75 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l73 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l76 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l74 sK1 sK0]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l76 sK0 sK1]
  have l78 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [← l77 sK0 sK1]
  have l79 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l80 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)))))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l6 X0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X1]
    conv => enter [1]; rw [l1 sK0 sK1 (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1))))]
  have l81 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l80 X0 sK0 sK1 X1]
    conv => enter [1]; rw [← l79 sK0 (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)))) sK1]
  have l82 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l81 X0 sK0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← l75 sK0 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1) X0]
  have l83 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l82 X0 sK0 X1 sK1]
    conv => enter [1, 2]; rw [← l75 sK0 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1) X1]
  have l84 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l83 X0 sK0 sK1 X1]
    conv => enter [1]; rw [← l54 sK0 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)]
  have l85 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l84 sK0 sK0 sK1 X1]
  have l86 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l85 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l87 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l85 sK0 sK1 X0]
  have l88 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1]; rw [l87 sK0 sK1 X0 X1]
  have l89 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [l88 sK0 sK1 X0 X1]
  have l90 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l79 sK0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [l89 sK0 sK0 X0 X1]
  have l91 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l86 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)]
  have l92 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l90 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l91 sK0 sK0 X0]
  have l93 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l65 sK0]
    conv => enter [1]; rw [← l92 sK0 X0]
  have l94 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l93 sK0 (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X1))))]
    conv => enter [1]; rw [← l18 X0 X1 (sK0 ◇ sK0) sK0]
  have l95 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l73 sK0 sK1]
    conv => enter [1, 2]; rw [l94 sK0 sK1 sK0]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0]
    conv => enter [1, 2]; rw [l95 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l96 x y]

theorem Equation4512_41661_implies_Equation41538 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41538 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l5 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l8 sK1 X0]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l7 sK1]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 sK1]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41661 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41661 X0 X1 X2]
  have l14 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l15 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41661 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l14 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l17 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l13 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
  have l18 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l16 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l19 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l17 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l20 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l18 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l21 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l20 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l22 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l15 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l23 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l15 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l15 (X0 ◇ X1) sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ sK1)]
  have l25 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l23 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l26 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l21 (sK1 ◇ sK1) (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l25 sK1 X0 X1]
  have l28 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l4 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l27 sK1 X0 X1]
  have l29 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [← l7 sK1]
    conv => enter [1]; rw [l28 sK1 X0 X1]
  have l30 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l29 sK1 X0 X1]
  have l31 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1]; rw [l30 sK1 X0 X1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l24 sK1]
  have l33 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41661 X0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK1]
  have l34 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l33 X0 sK1]
    conv => enter [1]; rw [l11 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l34 X0 sK1]
    conv => enter [1]; rw [← l31 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l36 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l15 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l37 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l15 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l38 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1]; rw [l35 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l39 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l19 X0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK1 sK1]
  have l40 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l15 (X0 ◇ (X1 ◇ X1)) sK1]
    conv => enter [1]; rw [l19 (X0 ◇ (X1 ◇ X1)) X0 X1]
    conv => enter [1, 2, 2]; rw [l15 (X0 ◇ (X1 ◇ X1)) sK1]
  have l41 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1, 2, 2]; rw [← l9 sK1 (X0 ◇ X0)]
  have l42 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) = ((sK1 ◇ sK1) ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [← l19 X2 X0 X1]
    conv => enter [1]; rw [l15 X2 sK1]
  have l43 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ X1)))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [l19 X0 (sK1 ◇ sK1) X1]
    conv => enter [1]; rw [l11 sK1 (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ X1))))]
  have l44 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ X1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l43 sK1 X0 X1]
    conv => enter [1]; rw [← l37 sK1 (X1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ X1))))]
  have l45 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1]; rw [l41 sK1 X0]
  have l46 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l40 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) (sK1 ◇ sK1)]
  have l47 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l39 X0 sK1]
    conv => enter [1]; rw [← l9 sK1 (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)))]
  have l48 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l42 (sK1 ◇ sK1) sK1 X0 sK1]
    conv => enter [1]; rw [← l44 sK1 X0 sK1]
  have l49 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l38 sK1]
    conv => enter [1]; rw [l45 sK1 X0]
  have l50 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l31 sK1 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l46 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l31 sK1 X0 (X1 ◇ X1)]
  have l51 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l47 X0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 sK1]
  have l52 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l49 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l48 sK1 X0]
  have l53 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l38 sK1]
    conv => enter [1]; rw [l50 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l38 sK1]
  have l54 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l51 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l55 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l52 sK1 sK1]
    conv => enter [1, 2]; rw [← l19 (sK1 ◇ sK1) sK1 sK1]
  have l56 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l54 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l53 sK1 X0 (sK1 ◇ sK1)]
  have l57 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l55 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l58 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l56 X0 sK1]
    conv => enter [1]; rw [← l53 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l59 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [← l57 sK1]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l59 sK1]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l59 sK1]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l61 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [← l63 sK0 sK1]
  have l65 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l64 sK0 sK1]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1]
    conv => enter [1]; rw [l65 sK1 sK0]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← l59 sK1]
  intro x y
  conv => enter [1]; rw [l67 x y]
  conv => enter [1]; rw [l66 y x]

theorem Equation4512_41661_implies_Equation41628 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41628 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41661 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l3 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l1 (X0 ◇ X1) sK0]
  have l9 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [l1 X0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l10 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41661 X0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [← l12 sK0 ((sK0 ◇ sK0) ◇ sK0) X0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l2 (sK1 ◇ (sK0 ◇ sK0)) sK1 sK0]
    conv => enter [1, 2]; rw [l14 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 (sK0 ◇ sK0) sK0]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l19 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2]; rw [l21 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation4512_41661_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation41534 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l1 sK1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41661 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41661 X0 X1 X2]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41661 (sK1 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 (X0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41661 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41661 X0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l9 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41661 X0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l10 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41661 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l8 X0 sK0 sK1]
  have l20 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← l18 sK1 sK0]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (X0 ◇ X0)]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (X0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l20 sK0 sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ (sK0 ◇ sK0)) sK1 sK0]
    conv => enter [1, 2]; rw [← l31 sK0 sK1]
  have l34 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0 sK0]
    conv => enter [1]; rw [← l33 sK0 sK0]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l34 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1 sK0]
    conv => enter [1, 2]; rw [← l37 sK0 sK1]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [← l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [← l42 sK1 sK0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1, 2]; rw [l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1, 2]; rw [l44 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l45 x y]

theorem Equation4512_41661_implies_Equation53904 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41661 : Equation41661 G) : Equation53904 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41661 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41661 X0 X1 X2]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (sK2 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [h41661 sK2 sK2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 X0]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41661 X0 X1 X2]
  have l4 : ∀ X0 sK2 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h41661 X0 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l3 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l5 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l6 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l7 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l10 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l9 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l11 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ ((X0 ◇ X1) ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ ((X0 ◇ X1) ◇ (sK2 ◇ sK2))))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l4 (X0 ◇ X1) sK2]
  have l12 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l13 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l11 sK2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l14 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l10 (sK2 ◇ sK2) (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [← l13 sK2 X0 X1]
  have l15 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l4 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [l14 sK2 X0 X1]
  have l16 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1, 2]; rw [l12 sK2]
    conv => enter [1]; rw [l0 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l17 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l16 sK2]
  have l18 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l17 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l19 : ∀ X0 sK2 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2
    conv => enter [1]; rw [h41661 X0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l17 sK2]
  have l20 : ∀ X0 sK2 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l19 X0 sK2]
    conv => enter [1]; rw [← l15 sK2 (sK2 ◇ sK2) X0]
  have l21 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l20 X0 sK2]
    conv => enter [1]; rw [← l17 sK2]
  have l22 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l18 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l23 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l21 X0 sK2]
  have l24 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l21 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [h41661 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l21 (X0 ◇ X1) sK2]
  have l25 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) sK2]
    conv => enter [1, 2]; rw [← l22 sK1 sK0 sK2]
  have l26 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l21 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
  have l27 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l26 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l28 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l27 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l29 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l21 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l28 sK1 sK0 sK2]
  have l30 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l8 X0 (X1 ◇ X1) X1]
  have l31 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) X3]
  have l32 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l31 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ (X2 ◇ X2))) X3]
  have l33 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l23 X0 X0 sK2]
    conv => enter [1]; rw [← l30 X1 X0]
  have l34 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l32 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) X3]
  have l35 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [← l33 sK2 X0 sK2]
  have l36 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l34 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) X3]
  have l37 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l36 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X2 X3]
  have l38 : ∀ X0 X3 X1 X2 sK2 : G, ((X0 ◇ X0) ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ X3))))) := by
    intro X0 X3 X1 X2 sK2
    conv => enter [1]; rw [l37 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [l23 X2 X3 sK2]
  have l39 : ∀ X0 X3 X1 X2 sK2 : G, ((X0 ◇ X0) ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 X3 X1 X2 sK2
    conv => enter [1]; rw [l38 X0 X3 X1 X2 sK2]
    conv => enter [1, 2, 2, 2, 2]; rw [← l35 sK2 X3]
  have l40 : ∀ X0 X3 X1 X2 sK2 : G, ((X0 ◇ X0) ◇ X3) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X3 X1 X2 sK2
    conv => enter [1]; rw [l39 X0 X3 X1 X2 sK2]
    conv => enter [1, 2, 2]; rw [← l24 sK2 X0 X1]
  have l41 : ∀ sK2 X0 X3 : G, (sK2 ◇ sK2) = ((X0 ◇ X0) ◇ X3) := by
    intro sK2 X0 X3
    conv => enter [1]; rw [l24 sK2 sK2 sK2]
    conv => enter [1]; rw [← l40 X0 X3 sK2 sK2 sK2]
  have l42 : ∀ sK2 X0 X3 : G, (sK2 ◇ sK2) = (X0 ◇ (X0 ◇ X3)) := by
    intro sK2 X0 X3
    conv => enter [1]; rw [l41 sK2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  intro x y z
  conv => enter [1]; rw [← l42 z x y]
  conv => enter [1]; rw [l29 z y x]

end Semigroup5
