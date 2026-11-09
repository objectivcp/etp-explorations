import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_42081_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42081 : Equation42081 G) : Equation39 G := by
  have l0 : ∀ X3 X2 X4 X0 X1 : G, (X3 ◇ X2) = (X4 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X4 X0 X1
    conv => enter [1]; rw [h42081 X3 X2 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X2 X0 X3 X4 X1 X5 : G, (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X1)))) = (X5 ◇ (X2 ◇ (X5 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X4 X1 X5
    conv => enter [1]; rw [h42081 X2 (X0 ◇ (X3 ◇ (X4 ◇ X1))) X5 X3]
    conv => enter [1, 2, 2, 2]; rw [← h42081 X0 X1 X3 X4]
  have l2 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h42081 X0 (sK0 ◇ sK0) X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h42081 X0 sK0 X0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← l2 X0 sK0 X0 X0]
  have l4 : ∀ X2 X0 X3 X4 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X1)))) = (X2 ◇ X1) := by
    intro X2 X0 X3 X4 X1
    conv => enter [1]; rw [l1 X2 X0 X3 X4 X1 X2]
    conv => enter [1]; rw [← h42081 X2 X1 X2 X0]
  have l5 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l0 X3 X2 X3 X3 X1]
    conv => enter [1]; rw [← h42081 X3 (X1 ◇ X2) X3 X3]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l8 : ∀ X0 X2 sK0 X1 : G, (X0 ◇ X2) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X2)))) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [h42081 X0 X2 sK0 X1]
    conv => enter [1, 2, 2]; rw [l7 sK0 (X1 ◇ X2)]
  have l9 : ∀ X0 X2 sK0 : G, (X0 ◇ X2) = (sK0 ◇ X2) := by
    intro X0 X2 sK0
    conv => enter [1]; rw [l8 X0 X2 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X0 (sK0 ◇ sK0) X0 X2]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation39_4512_implies_Equation42091 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42091 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ sK2) sK0]
    conv => enter [1, 1]; rw [h39 sK2 sK1]
    conv => enter [1, 2]; rw [h39 sK2 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
  have l8 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l7 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK2 sK3 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l2 sK0 sK2 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l8 sK3 sK1 sK0 sK2]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l9 sK0 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

theorem Equation4512_42091_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42091 : Equation42091 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42091 X0 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X1 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42091 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X4 ◇ (X1 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42091 X0 X1 X0 X0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0 X0]
    conv => enter [1, 2]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h42091 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [← l5 X0 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation39_4512_implies_Equation42096 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42096 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK3 sK2 X0 : G, (sK3 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK3]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK3 sK2 X0 : G, (sK0 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK3 ◇ sK2)) := by
    intro sK0 sK3 sK2 X0
    conv => enter [1]; rw [← h39 (sK3 ◇ sK2) sK0]
    conv => enter [1]; rw [h39 (sK3 ◇ sK2) X0]
  have l3 : ∀ sK0 sK3 sK2 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 sK1
    conv => enter [1]; rw [← h39 (sK3 ◇ sK2) sK0]
    conv => enter [1, 1]; rw [l1 sK3 sK2 sK1]
    conv => enter [1, 2]; rw [l1 sK3 sK2 sK1]
  have l4 : ∀ sK3 sK2 X0 X1 : G, (sK3 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [l1 sK3 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK0 sK3 sK2 X0 X1 : G, (sK0 ◇ (sK3 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK2))) := by
    intro sK0 sK3 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK3 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ sK2)]
  have l6 : ∀ sK0 sK3 sK2 X0 : G, (sK0 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK0 sK3 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK3 sK2 X0 sK0]
  have l7 : ∀ sK3 sK2 X0 : G, (sK3 ◇ sK2) = (X0 ◇ (sK3 ◇ sK2)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [l4 sK3 sK2 X0 sK3]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0]
  have l9 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK3 ◇ sK2)) sK3]
    conv => enter [1, 2]; rw [l6 sK0 sK3 sK2 sK1]
  have l10 : ∀ sK0 sK3 sK2 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK3 sK2 sK1
    conv => enter [1]; rw [l6 sK0 sK3 sK2 sK1]
    conv => enter [1]; rw [l9 sK1 sK0 sK3 sK2]
  have l11 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK2)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l8 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l3 sK0 sK3 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l11 x y w z]
  conv => enter [1]; rw [l10 w z y x]

theorem Equation4512_42096_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42096 : Equation42096 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X4 X3 X2 X0 X1 : G, (X4 ◇ X3) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X3 X2 X0 X1
    conv => enter [1]; rw [h42096 X4 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ sK1 X1 X0 sK0 : G, (sK1 ◇ X1) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0 sK0
    conv => enter [1]; rw [h42096 sK1 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 X4 X3 X2 : G, ((X0 ◇ X1) ◇ X4) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X0 X1 X4 X3 X2
    conv => enter [1]; rw [h42096 (X0 ◇ X1) X4 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l4 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = (X0 ◇ (X1 ◇ X4)) := by
    intro X3 X0 X1 X2 X4
    conv => enter [1]; rw [← l3 X0 X1 X4 X3 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l5 : ∀ sK1 X1 sK0 : G, (sK1 ◇ X1) = ((sK1 ◇ sK0) ◇ X1) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l2 sK1 X1 sK1 sK0]
    conv => enter [1]; rw [← h42096 (sK1 ◇ sK0) X1 sK1 sK0]
  have l6 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [← l4 X0 X0 X1 X0 X4]
    conv => enter [1]; rw [← l1 X0 X4 X0 X1 X0]
  have l7 : ∀ X0 X2 sK1 sK0 X1 : G, (X0 ◇ X2) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ X2)))) := by
    intro X0 X2 sK1 sK0 X1
    conv => enter [1]; rw [h42096 X0 X2 sK1 X1]
    conv => enter [1]; rw [l5 sK1 (X0 ◇ (X1 ◇ (sK1 ◇ X2))) sK0]
  have l8 : ∀ X0 X2 sK1 sK0 X1 : G, (X0 ◇ X2) = ((sK1 ◇ sK0) ◇ (X1 ◇ (sK1 ◇ X2))) := by
    intro X0 X2 sK1 sK0 X1
    conv => enter [1]; rw [l7 X0 X2 sK1 sK0 X1]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) X0 (X1 ◇ (sK1 ◇ X2))]
  have l9 : ∀ X0 X2 sK1 sK0 : G, (X0 ◇ X2) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X2)) := by
    intro X0 X2 sK1 sK0
    conv => enter [1]; rw [l8 X0 X2 sK1 sK0 X0]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) X0 (sK1 ◇ X2)]
  have l10 : ∀ X0 X2 sK1 sK0 : G, (X0 ◇ X2) = ((sK1 ◇ sK0) ◇ X2) := by
    intro X0 X2 sK1 sK0
    conv => enter [1]; rw [l9 X0 X2 sK1 sK0]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) sK1 X2]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK0]
    conv => enter [1]; rw [← l10 X0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x x y]

theorem Equation39_4512_implies_Equation42101 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42101 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK3 sK1 sK0 sK2 X0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) sK3]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) X0]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l5 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK0 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK2))]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK2 X0 sK1]
  have l7 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0 sK0]
  have l8 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 X0 sK1]
  have l10 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0 sK2 sK3]
  have l11 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l7 sK0 sK2 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK2)) sK1]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y w]
  conv => enter [1]; rw [l11 w y x]
  conv => enter [1]; rw [l10 x w y z]

theorem Equation4512_42101_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42101 : Equation42101 G) : Equation39 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42101 X0 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ X0) = (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h42101 X1 X0 X2 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X4 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42101 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X4 ◇ (X4 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X0 X2 X0]
    conv => enter [1]; rw [← h42101 X2 (X0 ◇ X1) X0 X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← l1 X0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l4 X0 sK0]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 X0]
  intro x y
  conv => enter [1]; rw [l6 x x y]

theorem Equation39_4512_implies_Equation42106 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42106 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK3 X0 : G, (sK0 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK0]
    conv => enter [1]; rw [h39 sK3 X0]
  have l2 : ∀ sK1 sK0 sK3 X0 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK0 sK3 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK3) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ sK3) X0]
  have l3 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ sK3) sK1]
    conv => enter [1, 1]; rw [l1 sK0 sK3 sK2]
    conv => enter [1, 2]; rw [l1 sK0 sK3 sK2]
  have l4 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ sK1 sK0 sK3 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK3)]
  have l6 : ∀ sK1 sK0 sK3 X0 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK3 X0 sK1]
  have l7 : ∀ sK0 sK3 X0 : G, (sK0 ◇ sK3) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l4 sK0 sK3 X0 sK0]
  have l8 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l7 sK2 sK3 X0]
  have l9 : ∀ sK4 sK2 sK1 sK0 sK3 : G, (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK4 sK2 sK1 sK0 sK3
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3))) sK4]
    conv => enter [1, 1]; rw [← l6 sK1 sK0 sK3 sK2]
    conv => enter [1, 2]; rw [← l6 sK1 sK0 sK3 sK2]
  have l10 : ∀ sK2 sK1 sK0 sK3 sK4 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK2 sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ (sK0 ◇ sK3)) (sK1 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [← l9 sK4 sK2 sK1 sK0 sK3]
  have l11 : ∀ sK1 sK0 sK3 sK4 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK0 sK3 sK4 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK3 sK2]
    conv => enter [1]; rw [l10 sK2 sK1 sK0 sK3 sK4]
  have l12 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l8 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l3 sK1 sK0 sK3 sK2]
  intro x y z w u
  conv => enter [1]; rw [l12 x y w u]
  conv => enter [1]; rw [l11 w u y z x]

theorem Equation4512_42106_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42106 : Equation42106 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 X1 X2 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (X2 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK0 X1 X2 sK1
    conv => enter [1]; rw [h42106 X0 (sK0 ◇ sK0) X1 X2 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK1 X1 X2 sK0 X0 : G, (sK1 ◇ X1) = (X2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X2 sK0 X0
    conv => enter [1]; rw [h42106 sK1 X1 X2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42106 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X4 ◇ (X5 ◇ X1)))]
  have l4 : ∀ X0 X1 X3 X5 : G, (X0 ◇ X1) = (X3 ◇ (X5 ◇ X1)) := by
    intro X0 X1 X3 X5
    conv => enter [1]; rw [l3 X0 X1 X0 X3 X0 X5]
    conv => enter [1]; rw [← h42106 X3 (X5 ◇ X1) X0 X0 X0]
  have l5 : ∀ sK1 X1 sK0 : G, (sK1 ◇ X1) = ((sK1 ◇ sK0) ◇ X1) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l2 sK1 X1 sK1 sK0 sK1]
    conv => enter [1]; rw [← h42106 (sK1 ◇ sK0) X1 sK1 sK0 sK1]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h42106 X0 sK0 X0 X0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← l1 X0 sK0 X0 X0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation39_4512_implies_Equation42116 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42116 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK2]
    conv => enter [1, 1]; rw [← l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l8 sK2 sK1 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_42116_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42116 : Equation42116 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42116 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42116 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h42116 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42116 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42116 X0 X1 X0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 X0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0 X0]
    conv => enter [1]; rw [← l5 X0 (sK0 ◇ sK0) (X0 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 sK1]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 ((sK1 ◇ sK0) ◇ sK0) sK1]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l5 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l5 (sK1 ◇ sK0) sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation39_4512_implies_Equation42120 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42120 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_42120_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42120 : Equation42120 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [h42120 X1 (sK0 ◇ X0) sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l2 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [h42120 X1 ((sK0 ◇ sK0) ◇ X0) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42120 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l4 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h42120 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42120 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h42120 X0 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l6 X0 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l8 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [l2 X1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))]
  have l9 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ (sK0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [l1 X1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X1 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h42120 X0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← l7 X0 sK0 X0]
  have l11 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [l8 X1 sK0 X0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))))]
  have l12 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [l9 X1 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l4 X1 sK0 X0 (X1 ◇ sK0)]
    conv => enter [1]; rw [← l11 X1 sK0 X0 X1]
  have l14 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ (sK0 ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42120 X1 X0 (X1 ◇ sK0)]
    conv => enter [1]; rw [← l12 X1 sK0 X0 X1]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l5 X0 sK0]
    conv => enter [1, 2]; rw [← l10 X0 sK0]
  have l17 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (X0 ◇ sK0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42120 X1 (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l5 X0 sK0]
  have l18 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l17 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (X1 ◇ (X0 ◇ sK0))]
  have l19 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (X1 ◇ (X0 ◇ sK0))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l18 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l13 X0 sK0 (X1 ◇ (X0 ◇ sK0))]
  have l20 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l19 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h42120 X1 sK0 X0]
  have l21 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l20 X1 X0 sK0]
    conv => enter [1]; rw [← l16 X1 sK0]
  have l22 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ sK0)) = (X1 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1, 2]; rw [l10 X0 sK0]
    conv => enter [1]; rw [l21 X1 X0 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l14 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l22 (sK1 ◇ sK0) sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l15 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l26 x y]

theorem Equation39_4512_implies_Equation42124 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42124 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK2]
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
  have l9 : ∀ sK3 sK2 sK1 sK0 : G, (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l3 sK1 sK0 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK3 sK2 sK1 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_42124_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42124 : Equation42124 G) : Equation39 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42124 sK0 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X4 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42124 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ (X4 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42124 X0 X1 X0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) (X0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l2 X0 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation39_4512_implies_Equation42133 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42133 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l5 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK1]
  have l8 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK2]
    conv => enter [1, 1]; rw [← l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l8 sK2 sK1 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation42133_implies_Equation39 (G : Type*) [Magma G] (h42133 : Equation42133 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42133 X0 X1 X0]
    conv => enter [1]; rw [← h42133 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42137 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42137 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK2 sK1]
    conv => enter [1, 2]; rw [l8 sK1 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation42137_implies_Equation39 (G : Type*) [Magma G] (h42137 : Equation42137 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42137 X0 X1 X0]
    conv => enter [1]; rw [← h42137 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42141 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42141 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l7 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l3 sK2 sK0 sK2 sK2]
    conv => enter [1, 2]; rw [l6 sK2 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 sK0]
  have l9 : ∀ sK3 sK2 sK0 sK1 : G, (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [l3 sK2 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l9 sK3 sK2 sK0 sK2]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

@[equational_result]
theorem Equation42141_implies_Equation39 (G : Type*) [Magma G] (h42141 : Equation42141 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42141 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42141 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42150 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42150 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [h39 sK1 sK0]
    conv => enter [1]; rw [l0 sK2 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h39 sK1 sK0]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l5 sK2 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 sK1]
  have l8 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l7 sK2 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation42150_implies_Equation39 (G : Type*) [Magma G] (h42150 : Equation42150 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42150 X0 X1 X0]
    conv => enter [1]; rw [← h42150 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42154 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42154 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK2 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l7 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l6 sK2 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK2 sK1]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l8 sK2 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation42154_implies_Equation39 (G : Type*) [Magma G] (h42154 : Equation42154 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42154 X0 X1 X0]
    conv => enter [1]; rw [← h42154 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42158 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42158 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK3 sK0 sK2 X0 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK3 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l7 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK2 sK3]
    conv => enter [1, 2]; rw [l6 sK3 sK2 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l7 sK3 sK0 sK2]
  have l9 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK3 sK3]
    conv => enter [1, 2]; rw [l8 sK3 sK2 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l9 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

@[equational_result]
theorem Equation42158_implies_Equation39 (G : Type*) [Magma G] (h42158 : Equation42158 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42158 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42158 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42168 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42168 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ sK2) sK0]
    conv => enter [1, 1]; rw [h39 sK2 sK1]
    conv => enter [1, 2]; rw [h39 sK2 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2 sK2 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK0 sK2]
  have l8 : ∀ sK3 sK2 sK0 sK1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l7 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK0 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l8 sK3 sK2 sK0 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l9 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

@[equational_result]
theorem Equation42168_implies_Equation39 (G : Type*) [Magma G] (h42168 : Equation42168 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42168 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42168 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42173 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42173 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK3]
  have l1 : ∀ sK0 sK3 sK2 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 sK1
    conv => enter [1]; rw [← h39 (sK3 ◇ sK2) sK0]
    conv => enter [1, 1]; rw [l0 sK3 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK3 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK0 sK3 sK2 X0 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 X0 sK1
    conv => enter [1]; rw [l1 sK0 sK3 sK2 sK1]
    conv => enter [1]; rw [h39 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK2)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK0 sK3 sK2 sK1]
  have l7 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l3 sK0 sK3 sK2 sK2 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK2 sK0 sK3]
  have l8 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l7 sK0 sK3 sK2]
  have l9 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l3 sK0 sK3 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK2 sK0 sK3]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l9 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

@[equational_result]
theorem Equation42173_implies_Equation39 (G : Type*) [Magma G] (h42173 : Equation42173 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42173 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42173 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42178 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42178 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2 sK2 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK0 sK2]
  have l9 : ∀ sK3 sK2 sK0 sK1 : G, (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l3 sK0 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l9 sK3 sK2 sK0 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

@[equational_result]
theorem Equation42178_implies_Equation39 (G : Type*) [Magma G] (h42178 : Equation42178 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42178 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42178 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42183 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42183 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK0]
  have l1 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ sK3) sK1]
    conv => enter [1, 1]; rw [l0 sK0 sK3 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK2]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l3 : ∀ sK1 sK0 sK3 X0 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 X0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK3 sK2]
    conv => enter [1]; rw [h39 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0 sK2]
  have l6 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l1 sK1 sK0 sK3 sK2]
  have l7 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l3 sK1 sK0 sK3 sK3 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK3 sK1 sK0]
  have l8 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 sK3]
  have l9 : ∀ sK4 sK3 sK1 sK0 sK2 : G, (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK4 sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h39 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) sK4]
    conv => enter [1, 1]; rw [← l8 sK2 sK3 sK1 sK0]
    conv => enter [1, 2]; rw [← l8 sK2 sK3 sK1 sK0]
  have l10 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l3 sK1 sK0 sK3 (sK1 ◇ sK3) sK1]
    conv => enter [1]; rw [← l9 sK4 sK3 sK1 sK0 sK1]
  have l11 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l10 sK1 sK0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l11 x y z w u]

@[equational_result]
theorem Equation42183_implies_Equation39 (G : Type*) [Magma G] (h42183 : Equation42183 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42183 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42183 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42271 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42271 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h39 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 sK0]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l8 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l6 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK3]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [← h39 sK2 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1, 1]; rw [← l9 sK1 sK2]
    conv => enter [1, 2]; rw [← l9 sK1 sK2]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l10 sK0 sK1 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y w]
  conv => enter [1]; rw [l8 w x y z]

theorem Equation4512_42271_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42271 : Equation42271 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h42271 sK1 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h42271 sK1 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42271 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42271 X0 X1 X0 X0]
  have l5 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 X0 X1]
  have l6 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ sK0) ◇ sK0) = (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l5 sK1 sK0 sK1 X1]
    conv => enter [1]; rw [← l4 X1 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l7 : ∀ sK1 sK0 X1 : G, (sK1 ◇ sK0) = (X1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK1 X1]
    conv => enter [1]; rw [← l4 X1 ((sK1 ◇ sK0) ◇ sK0) sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42271 sK0 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK1 sK0 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0 sK1]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK0) sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation39_4512_implies_Equation42276 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42276 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK3 sK2 X0 : G, (sK3 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK3]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK1 sK3 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK3 ◇ sK2))) := by
    intro sK0 sK1 sK3 sK2 X0
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK3 ◇ sK2)) sK0]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK3 ◇ sK2)) X0]
  have l3 : ∀ sK1 sK3 sK2 X0 : G, (sK1 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK3 sK2 X0
    conv => enter [1, 2]; rw [l1 sK3 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK3 sK2 X0 X1 : G, (sK3 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [l1 sK3 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK0 sK1 sK3 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK1 sK3 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK3 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK3 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK3 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK1 sK3 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK3 sK2 X0 sK0]
  have l7 : ∀ sK3 sK2 X0 : G, (sK3 ◇ sK2) = (X0 ◇ (sK3 ◇ sK2)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [l4 sK3 sK2 X0 sK3]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0]
  have l9 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l10 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK3 ◇ sK2)) sK0]
    conv => enter [1, 1]; rw [← l9 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK3]
  have l11 : ∀ sK1 sK3 sK2 sK0 : G, (sK1 ◇ (sK3 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK3 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l10 sK0 sK1 sK3 sK2]
  have l12 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK3 ◇ sK2))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l9 sK1 sK2 sK3]
    conv => enter [1]; rw [l11 sK1 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y w z]
  conv => enter [1]; rw [l6 w x z y z]

theorem Equation4512_42276_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42276 : Equation42276 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X1 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [h42276 (sK0 ◇ sK0) X1 X0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0 (X0 ◇ X1)]
  have l2 : ∀ X2 X4 X3 X0 X1 : G, (X2 ◇ X4) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X3 X0 X1
    conv => enter [1]; rw [h42276 X2 X4 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42276 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X1)))]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X1)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l3 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X3 X1]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42276 sK0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 X1 sK0 sK0]
  have l6 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X3 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l4 X0 X1 X0 X3 X0]
    conv => enter [1]; rw [← l2 X0 (X3 ◇ X1) X0 X3 X0]
  have l7 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2)))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h42276 X1 X2 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [l5 sK0 X2]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l7 X1 X2 sK0 X1]
    conv => enter [1, 2]; rw [← l6 X1 ((sK0 ◇ sK0) ◇ X2) X1]
  have l9 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l8 X1 X2 sK0]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ sK0) ◇ X2) X1]
  have l10 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ X2) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l9 X1 X2 sK0]
    conv => enter [1]; rw [← l6 sK0 X2 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l10 x x y]

theorem Equation39_4512_implies_Equation42281 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42281 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK3 sK0 sK1 sK2 X0 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK3]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
  have l2 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK0 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 sK0]
  have l7 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X0 sK1]
  have l8 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 X0 sK1]
  have l10 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK3 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK1 sK2 sK3]
  have l11 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l12 x y w]
  conv => enter [1]; rw [l11 x w y]
  conv => enter [1]; rw [l10 w x y z]

theorem Equation4512_42281_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42281 : Equation42281 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42281 X0 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h42281 sK1 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK0 X0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42281 X0 X1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ X1))]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X4 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42281 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X0 ◇ (X4 ◇ X1)))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42281 X0 X1 X0 X0]
  have l6 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ X0) := by
    intro X1 sK1 sK0 X0
    conv => enter [1, 2]; rw [l3 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l2 sK1 X0 X1 sK0]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l3 X0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK0 X0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0 X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0 X0]
    conv => enter [1]; rw [← l9 X0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l8 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation39_4512_implies_Equation42286 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42286 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK3 X0 : G, (sK0 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK0]
    conv => enter [1]; rw [h39 sK3 X0]
  have l2 : ∀ sK1 sK2 sK0 sK3 X0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK0 ◇ sK3)) sK1]
    conv => enter [1]; rw [h39 (sK2 ◇ (sK0 ◇ sK3)) X0]
  have l3 : ∀ sK2 sK0 sK3 X0 : G, (sK2 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK0 sK3 X0
    conv => enter [1, 2]; rw [l1 sK0 sK3 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ sK1 sK2 sK0 sK3 X0 X1 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK0 sK3 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK0 ◇ sK3))]
  have l6 : ∀ sK1 sK2 sK0 sK3 X0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [l5 sK1 sK2 sK0 sK3 X0 sK1]
  have l7 : ∀ sK0 sK3 X0 : G, (sK0 ◇ sK3) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l4 sK0 sK3 X0 sK0]
  have l8 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l7 sK2 sK3 X0]
  have l9 : ∀ sK1 sK2 sK0 sK3 sK4 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (sK4 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK0 sK3 sK4
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK3 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3)))]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) sK4]
  have l10 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK2 sK3 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l11 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK0 ◇ sK3)) sK1]
    conv => enter [1, 1]; rw [← l10 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l10 sK2 sK3 sK0]
  have l12 : ∀ sK2 sK0 sK3 sK1 : G, (sK2 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK0 sK3 sK1
    conv => enter [1]; rw [l3 sK2 sK0 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0 sK3]
  have l13 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK3 sK0]
    conv => enter [1]; rw [l12 sK2 sK0 sK3 sK1]
  intro x y z w u
  conv => enter [1]; rw [l13 x y w u]
  conv => enter [1]; rw [l9 w x u y z]

theorem Equation4512_42286_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42286 : Equation42286 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 X1 X2 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK0 X1 X2 sK1
    conv => enter [1]; rw [h42286 X0 (sK0 ◇ sK0) X1 X2 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK1 X0 X1 X2 sK0 : G, (sK1 ◇ X0) = (X1 ◇ (X2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK1 X0 X1 X2 sK0
    conv => enter [1]; rw [h42286 sK1 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK0 X0]
  have l3 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X5 ◇ X1))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42286 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X4 ◇ (X0 ◇ (X5 ◇ X1)))]
  have l4 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ (X5 ◇ X1)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [l3 X0 X1 X0 X0 X4 X5]
    conv => enter [1]; rw [← h42286 X4 (X5 ◇ X1) X0 X0 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42286 (sK1 ◇ sK0) X0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 X0 sK1 sK1 sK0]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h42286 X0 sK0 X0 X0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← l1 X0 sK0 X0 X0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l5 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation39_4512_implies_Equation42297 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42297 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1]; rw [h39 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l3 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 X0 sK1
    conv => enter [1, 2]; rw [h39 sK2 sK1]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK2 X0 sK0]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l8 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l6 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) sK3]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [← h39 sK2 sK1]
  have l10 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1, 1]; rw [← l9 sK1 sK2]
    conv => enter [1, 2]; rw [← l9 sK1 sK2]
  have l11 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l10 sK0 sK2 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [l11 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y w]
  conv => enter [1]; rw [l8 w y z]

@[equational_result]
theorem Equation42297_implies_Equation39 (G : Type*) [Magma G] (h42297 : Equation42297 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42297 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42297 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42302 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42302 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ (sK2 ◇ (sK3 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK3 ◇ sK2)) sK0]
    conv => enter [1]; rw [h39 (sK2 ◇ (sK3 ◇ sK2)) X0]
  have l4 : ∀ sK2 sK3 X0 sK1 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 X0 sK1
    conv => enter [1, 2]; rw [l0 sK3 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK0 sK2 sK3 X0 X1 : G, (sK0 ◇ (sK2 ◇ (sK3 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK2 sK3 X0 X1
    conv => enter [1]; rw [l3 sK0 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK3 ◇ sK2))]
  have l7 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ (sK2 ◇ (sK3 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [l6 sK0 sK2 sK3 X0 sK0]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK3 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l8 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK3]
  have l10 : ∀ sK0 sK2 sK3 sK1 : G, (sK0 ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [← h39 (sK2 ◇ (sK3 ◇ sK2)) sK0]
    conv => enter [1, 1]; rw [← l9 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK3]
  have l11 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK2 sK3 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l10 sK0 sK2 sK3 sK2]
  have l12 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l9 sK1 sK2 sK3]
    conv => enter [1]; rw [l11 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l12 x y w z]
  conv => enter [1]; rw [l7 w y z z]

@[equational_result]
theorem Equation42302_implies_Equation39 (G : Type*) [Magma G] (h42302 : Equation42302 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42302 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42302 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42307 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42307 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
  have l7 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l3 sK2 sK0 sK0 sK2]
    conv => enter [1, 2]; rw [l6 sK2 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 sK0]
  have l9 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [l3 sK2 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l9 sK3 sK0 sK2 sK2]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

@[equational_result]
theorem Equation42307_implies_Equation39 (G : Type*) [Magma G] (h42307 : Equation42307 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42307 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42307 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42312 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42312 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l3 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h39 (sK3 ◇ (sK0 ◇ sK3)) sK1]
    conv => enter [1]; rw [h39 (sK3 ◇ (sK0 ◇ sK3)) X0]
  have l4 : ∀ sK3 sK0 X0 sK2 : G, (sK3 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK3 sK0 X0 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK2]
    conv => enter [1]; rw [l1 sK3 (sK2 ◇ sK3) X0]
  have l5 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l6 : ∀ sK1 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l3 sK1 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ (sK0 ◇ sK3))]
  have l7 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK3 sK0 X0 sK1]
  have l8 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l5 sK2 sK3 X0 sK2]
  have l9 : ∀ sK1 sK3 sK0 sK4 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (sK4 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0 sK4
    conv => enter [1]; rw [l7 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK4]
  have l10 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK2 sK3 sK3]
    conv => enter [1, 2]; rw [l0 sK2 sK3 sK0]
  have l11 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h39 (sK3 ◇ (sK0 ◇ sK3)) sK1]
    conv => enter [1, 1]; rw [← l10 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l10 sK2 sK3 sK0]
  have l12 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l4 sK3 sK0 (sK3 ◇ sK3) sK3]
    conv => enter [1]; rw [← l11 sK1 sK3 sK0 sK3]
  have l13 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK3 sK0]
    conv => enter [1]; rw [l12 sK3 sK0 sK1]
  intro x y z w u
  conv => enter [1]; rw [l13 x y w u]
  conv => enter [1]; rw [l9 w y u z]

@[equational_result]
theorem Equation42312_implies_Equation39 (G : Type*) [Magma G] (h42312 : Equation42312 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42312 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42312 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42323 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42323 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK3 sK2 X0 : G, (sK0 ◇ (sK3 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK3 sK2 X0
    conv => enter [1]; rw [← h39 (sK3 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1]; rw [h39 (sK3 ◇ (sK2 ◇ sK2)) X0]
  have l3 : ∀ sK3 sK2 X0 sK1 : G, (sK3 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK2 X0 sK1
    conv => enter [1, 2]; rw [h39 sK2 sK1]
    conv => enter [1]; rw [l0 sK3 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK0 sK3 sK2 X0 X1 : G, (sK0 ◇ (sK3 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK3 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK3 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK0 sK3 sK2 X0 : G, (sK0 ◇ (sK3 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK3 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK3 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK3 sK2 X0 sK0]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l8 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l7 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← h39 sK2 sK1]
  have l9 : ∀ sK0 sK3 sK2 sK1 : G, (sK0 ◇ (sK3 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 sK1
    conv => enter [1]; rw [← h39 (sK3 ◇ (sK2 ◇ sK2)) sK0]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK3]
  have l10 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK3 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [l3 sK3 sK2 (sK3 ◇ sK2) sK3]
    conv => enter [1]; rw [← l9 sK0 sK3 sK2 sK3]
  have l11 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l8 sK1 sK2 sK3]
    conv => enter [1]; rw [l10 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l11 x y w z]
  conv => enter [1]; rw [l6 w z y z]

@[equational_result]
theorem Equation42323_implies_Equation39 (G : Type*) [Magma G] (h42323 : Equation42323 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42323 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42323 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42328 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42328 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK3 sK2 X0 : G, (sK0 ◇ (sK3 ◇ (sK3 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK2))) := by
    intro sK0 sK3 sK2 X0
    conv => enter [1]; rw [← h39 (sK3 ◇ (sK3 ◇ sK2)) sK0]
    conv => enter [1]; rw [h39 (sK3 ◇ (sK3 ◇ sK2)) X0]
  have l3 : ∀ sK3 sK2 X0 sK1 : G, (sK3 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK2 X0 sK1
    conv => enter [1, 2]; rw [l1 sK3 sK2 sK1]
    conv => enter [1]; rw [l0 sK3 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK0 sK3 sK2 X0 X1 : G, (sK0 ◇ (sK3 ◇ (sK3 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK3 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK3 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ (sK3 ◇ sK2))]
  have l6 : ∀ sK0 sK3 sK2 X0 : G, (sK0 ◇ (sK3 ◇ (sK3 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK3 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK3 sK2 X0 sK0]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l8 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l7 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3]
  have l9 : ∀ sK0 sK3 sK2 sK1 : G, (sK0 ◇ (sK3 ◇ (sK3 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 sK1
    conv => enter [1]; rw [← h39 (sK3 ◇ (sK3 ◇ sK2)) sK0]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK3]
  have l10 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK3 ◇ sK2)) = (sK0 ◇ (sK3 ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [l3 sK3 sK2 (sK3 ◇ sK2) sK3]
    conv => enter [1]; rw [← l9 sK0 sK3 sK2 sK3]
  have l11 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK3 ◇ sK2))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l8 sK1 sK2 sK3]
    conv => enter [1]; rw [l10 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l11 x y w z]
  conv => enter [1]; rw [l6 w z y z]

@[equational_result]
theorem Equation42328_implies_Equation39 (G : Type*) [Magma G] (h42328 : Equation42328 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42328 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42328 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42333 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42333 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK3 sK0 sK2 X0 sK1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK3 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l6 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l2 sK3 sK0 sK2 sK0 sK3]
    conv => enter [1, 2]; rw [l5 sK3 sK2 sK3 sK0]
  have l7 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l6 sK3 sK0 sK2]
  have l8 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l2 sK3 sK0 sK2 sK3 sK3]
    conv => enter [1, 2]; rw [l7 sK3 sK2 sK0 sK3]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l8 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

@[equational_result]
theorem Equation42333_implies_Equation39 (G : Type*) [Magma G] (h42333 : Equation42333 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42333 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42333 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42338 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42338 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l3 : ∀ sK1 sK4 sK0 sK3 X0 : G, (sK1 ◇ (sK4 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK4 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK4 sK0 sK3 X0
    conv => enter [1]; rw [← h39 (sK4 ◇ (sK0 ◇ sK3)) sK1]
    conv => enter [1]; rw [h39 (sK4 ◇ (sK0 ◇ sK3)) X0]
  have l4 : ∀ sK4 sK0 sK3 X0 sK2 : G, (sK4 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK4 sK0 sK3 X0 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK2]
    conv => enter [1]; rw [l1 sK4 (sK2 ◇ sK3) X0]
  have l5 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l6 : ∀ sK1 sK4 sK0 sK3 X0 X1 : G, (sK1 ◇ (sK4 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK4 sK0 sK3 X0 X1
    conv => enter [1]; rw [l3 sK1 sK4 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK4 ◇ (sK0 ◇ sK3))]
  have l7 : ∀ sK1 sK4 sK0 sK3 X0 : G, (sK1 ◇ (sK4 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK4 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK4 sK0 sK3 X0
    conv => enter [1]; rw [l6 sK1 sK4 sK0 sK3 X0 sK1]
  have l8 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l5 sK2 sK3 X0 sK2]
  have l9 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [l8 sK2 sK3 sK4]
    conv => enter [1, 2]; rw [l0 sK2 sK3 sK0]
  have l10 : ∀ sK1 sK4 sK0 sK3 sK2 : G, (sK1 ◇ (sK4 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK4 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK4 ◇ (sK0 ◇ sK3)) sK1]
    conv => enter [1, 1]; rw [← l9 sK2 sK3 sK4 sK0]
    conv => enter [1, 2]; rw [← l9 sK2 sK3 sK4 sK0]
  have l11 : ∀ sK4 sK0 sK3 sK1 : G, (sK4 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK4 ◇ (sK0 ◇ sK3))) := by
    intro sK4 sK0 sK3 sK1
    conv => enter [1]; rw [l4 sK4 sK0 sK3 (sK4 ◇ sK3) sK4]
    conv => enter [1]; rw [← l10 sK1 sK4 sK0 sK3 sK4]
  have l12 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK4 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l9 sK2 sK3 sK4 sK0]
    conv => enter [1]; rw [l11 sK4 sK0 sK3 sK1]
  intro x y z w u
  conv => enter [1]; rw [l12 x y w z u]
  conv => enter [1]; rw [l7 w z u y z]

@[equational_result]
theorem Equation42338_implies_Equation39 (G : Type*) [Magma G] (h42338 : Equation42338 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42338 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42338 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42349 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42349 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [h39 sK2 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h39 sK2 sK1]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK0 sK2]
  have l8 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l7 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK0 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l8 sK3 sK0 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l9 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

@[equational_result]
theorem Equation42349_implies_Equation39 (G : Type*) [Magma G] (h42349 : Equation42349 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42349 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42349 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42354 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42354 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ sK2) = (sK3 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 sK3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK0 sK3 sK2 X0 sK1 : G, (sK0 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK3 sK2 X0 sK1
    conv => enter [1, 2]; rw [l0 sK3 sK2 sK1]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
  have l6 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK3 ◇ sK2)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK3]
  have l7 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l3 sK0 sK3 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK2 sK0 sK3]
  have l8 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l7 sK0 sK3 sK2]
  have l9 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l3 sK0 sK3 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK2 sK0 sK3]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [l9 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

@[equational_result]
theorem Equation42354_implies_Equation39 (G : Type*) [Magma G] (h42354 : Equation42354 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42354 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42354 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42359 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42359 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK0 sK2]
  have l8 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) sK3]
    conv => enter [1, 1]; rw [← l7 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK0 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l8 sK3 sK0 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l9 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

@[equational_result]
theorem Equation42359_implies_Equation39 (G : Type*) [Magma G] (h42359 : Equation42359 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42359 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42359 X2 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42364 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42364 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l3 : ∀ sK1 sK0 sK3 X0 sK2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 X0 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK2]
    conv => enter [1]; rw [l1 sK1 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0 sK2]
  have l6 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l0 sK2 sK3 sK0]
  have l7 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l3 sK1 sK0 sK3 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK3 sK1 sK0]
  have l8 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 sK3]
  have l9 : ∀ sK4 sK1 sK0 sK3 sK2 : G, (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK4 sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3))) sK4]
    conv => enter [1, 1]; rw [← l8 sK2 sK3 sK1 sK0]
    conv => enter [1, 2]; rw [← l8 sK2 sK3 sK1 sK0]
  have l10 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ sK3)) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l3 sK1 sK0 sK3 (sK1 ◇ sK3) sK1]
    conv => enter [1]; rw [← l9 sK4 sK1 sK0 sK3 sK1]
  have l11 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l10 sK1 sK0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l11 x y z w u]

@[equational_result]
theorem Equation42364_implies_Equation39 (G : Type*) [Magma G] (h42364 : Equation42364 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42364 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42364 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42376 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42376 G := by
  have l0 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK3 ◇ sK3) sK0]
    conv => enter [1, 1]; rw [h39 sK3 sK2]
    conv => enter [1, 2]; rw [h39 sK3 sK2]
  have l1 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l2 : ∀ sK0 sK3 X0 sK2 : G, (sK0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK3 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK3 sK2]
    conv => enter [1]; rw [h39 (sK2 ◇ sK3) X0]
  have l3 : ∀ sK1 sK0 sK3 X0 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK1 sK0 sK3 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK3 ◇ sK3)) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK3 ◇ sK3)) X0]
  have l4 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ sK1 sK0 sK3 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [l3 sK1 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK3 ◇ sK3))]
  have l6 : ∀ sK1 sK0 sK3 X0 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK1 sK0 sK3 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK3 X0 sK1]
  have l7 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0 sK2]
  have l8 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l6 sK1 sK0 sK3 (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3)))]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) sK4]
  have l9 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l7 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l0 sK0 sK3 sK2]
  have l10 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK3 ◇ sK3)) sK1]
    conv => enter [1, 1]; rw [← l9 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l9 sK2 sK3 sK0]
  have l11 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ (sK3 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [l2 sK0 sK3 (sK0 ◇ sK3) sK0]
    conv => enter [1]; rw [← l10 sK1 sK0 sK3 sK0]
  have l12 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK3 sK0]
    conv => enter [1]; rw [l11 sK0 sK3 sK1]
  intro x y z w u
  conv => enter [1]; rw [l12 x y w u]
  conv => enter [1]; rw [l8 w u y z]

@[equational_result]
theorem Equation42376_implies_Equation39 (G : Type*) [Magma G] (h42376 : Equation42376 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42376 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42376 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42382 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42382 G := by
  have l0 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ sK3) = (sK4 ◇ sK3) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK4]
  have l1 : ∀ sK0 sK4 sK3 sK2 : G, (sK0 ◇ (sK4 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK4 sK3 sK2
    conv => enter [1]; rw [← h39 (sK4 ◇ sK3) sK0]
    conv => enter [1, 1]; rw [l0 sK4 sK3 sK2]
    conv => enter [1, 2]; rw [l0 sK4 sK3 sK2]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l3 : ∀ sK0 sK4 sK3 X0 sK2 : G, (sK0 ◇ (sK4 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK4 sK3 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK4 sK3 sK2]
    conv => enter [1]; rw [h39 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK1 sK0 sK4 sK3 X0 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) = (X0 ◇ (sK0 ◇ (sK4 ◇ sK3))) := by
    intro sK1 sK0 sK4 sK3 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK4 ◇ sK3)) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK4 ◇ sK3)) X0]
  have l5 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l6 : ∀ sK1 sK0 sK4 sK3 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK4 ◇ sK3)))) := by
    intro sK1 sK0 sK4 sK3 X0 X1
    conv => enter [1]; rw [l4 sK1 sK0 sK4 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK4 ◇ sK3))]
  have l7 : ∀ sK1 sK0 sK4 sK3 X0 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3)))) := by
    intro sK1 sK0 sK4 sK3 X0
    conv => enter [1]; rw [l6 sK1 sK0 sK4 sK3 X0 sK1]
  have l8 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l5 sK2 sK3 X0 sK2]
  have l9 : ∀ sK2 sK3 sK0 sK4 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK4 ◇ sK3)) := by
    intro sK2 sK3 sK0 sK4
    conv => enter [1]; rw [l8 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l1 sK0 sK4 sK3 sK2]
  have l10 : ∀ sK1 sK0 sK4 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK4 sK3 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK4 ◇ sK3)) sK1]
    conv => enter [1, 1]; rw [← l9 sK2 sK3 sK0 sK4]
    conv => enter [1, 2]; rw [← l9 sK2 sK3 sK0 sK4]
  have l11 : ∀ sK0 sK4 sK3 sK1 : G, (sK0 ◇ (sK4 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) := by
    intro sK0 sK4 sK3 sK1
    conv => enter [1]; rw [l3 sK0 sK4 sK3 (sK0 ◇ sK3) sK0]
    conv => enter [1]; rw [← l10 sK1 sK0 sK4 sK3 sK0]
  have l12 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l9 sK2 sK3 sK0 sK4]
    conv => enter [1]; rw [l11 sK0 sK4 sK3 sK1]
  intro x y z w u
  conv => enter [1]; rw [l12 x y w u z]
  conv => enter [1]; rw [l7 w u z y z]

@[equational_result]
theorem Equation42382_implies_Equation39 (G : Type*) [Magma G] (h42382 : Equation42382 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42382 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42382 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42388 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42388 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l2 : ∀ sK0 sK1 sK3 X0 : G, (sK0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK1 ◇ sK3)) := by
    intro sK0 sK1 sK3 X0
    conv => enter [1]; rw [← h39 (sK1 ◇ sK3) sK0]
    conv => enter [1]; rw [h39 (sK1 ◇ sK3) X0]
  have l3 : ∀ sK0 sK1 sK3 sK2 : G, (sK0 ◇ (sK1 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [← h39 (sK1 ◇ sK3) sK0]
    conv => enter [1, 1]; rw [l1 sK1 sK3 sK2]
    conv => enter [1, 2]; rw [l1 sK1 sK3 sK2]
  have l4 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ sK0 sK1 sK3 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) := by
    intro sK0 sK1 sK3 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK3)]
  have l6 : ∀ sK0 sK1 sK3 X0 : G, (sK0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK0 sK1 sK3 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK3 X0 sK0]
  have l7 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0 sK2]
  have l8 : ∀ sK4 sK1 sK0 sK3 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK3)))) = ((sK0 ◇ (sK1 ◇ sK3)) ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h39 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK3))) sK4]
    conv => enter [1, 1]; rw [← l6 sK0 sK1 sK3 sK1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK3 sK1]
  have l9 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK3)) (sK0 ◇ (sK1 ◇ sK3))]
    conv => enter [1]; rw [← l8 sK4 sK1 sK0 sK3]
  have l10 : ∀ sK0 sK1 sK3 sK4 : G, (sK0 ◇ (sK1 ◇ sK3)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK0 sK1 sK3 sK4
    conv => enter [1]; rw [l6 sK0 sK1 sK3 sK1]
    conv => enter [1]; rw [l9 sK1 sK0 sK3 sK4]
  have l11 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK1 ◇ sK3)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l7 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l3 sK0 sK1 sK3 sK2]
  intro x y z w u
  conv => enter [1]; rw [l11 x y u w]
  conv => enter [1]; rw [l10 u w y z]

@[equational_result]
theorem Equation42388_implies_Equation39 (G : Type*) [Magma G] (h42388 : Equation42388 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42388 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42388 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42394 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42394 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l2 : ∀ sK1 sK0 sK3 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK0 sK3 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK0 ◇ sK3)) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK0 ◇ sK3)) X0]
  have l3 : ∀ sK0 sK3 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK3 X0 sK2
    conv => enter [1, 2]; rw [l1 sK0 sK3 sK2]
    conv => enter [1]; rw [l0 sK0 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l5 : ∀ sK1 sK0 sK3 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK0 sK3 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK3))]
  have l6 : ∀ sK1 sK0 sK3 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK0 sK3 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK3 X0 sK1]
  have l7 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK3 X0 sK2]
  have l8 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3))) = (sK4 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l6 sK1 sK0 sK3 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3)))]
    conv => enter [1]; rw [h39 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3))) sK4]
  have l9 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l7 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK0]
  have l10 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK0 ◇ sK3)) sK1]
    conv => enter [1, 1]; rw [← l9 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l9 sK2 sK3 sK0]
  have l11 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [l3 sK0 sK3 (sK0 ◇ sK3) sK0]
    conv => enter [1]; rw [← l10 sK1 sK0 sK3 sK0]
  have l12 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK3 sK0]
    conv => enter [1]; rw [l11 sK0 sK3 sK1]
  intro x y z w u
  conv => enter [1]; rw [l12 x y w u]
  conv => enter [1]; rw [l8 w u y z]

@[equational_result]
theorem Equation42394_implies_Equation39 (G : Type*) [Magma G] (h42394 : Equation42394 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42394 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42394 X2 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42400 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42400 G := by
  have l0 : ∀ sK3 sK4 sK1 : G, (sK3 ◇ sK4) = (sK1 ◇ sK4) := by
    intro sK3 sK4 sK1
    conv => enter [1]; rw [← h39 sK4 sK3]
    conv => enter [1]; rw [h39 sK4 sK1]
  have l1 : ∀ sK0 sK1 sK4 sK3 : G, (sK0 ◇ (sK1 ◇ sK4)) = ((sK3 ◇ sK4) ◇ (sK3 ◇ sK4)) := by
    intro sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← h39 (sK1 ◇ sK4) sK0]
    conv => enter [1, 1]; rw [l0 sK1 sK4 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK4 sK3]
  have l2 : ∀ sK3 sK4 X0 : G, (sK3 ◇ sK4) = (X0 ◇ sK4) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [← h39 sK4 sK3]
    conv => enter [1]; rw [h39 sK4 X0]
  have l3 : ∀ sK0 sK1 sK4 X0 sK3 : G, (sK0 ◇ (sK1 ◇ sK4)) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK0 sK1 sK4 X0 sK3
    conv => enter [1]; rw [l1 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [h39 (sK3 ◇ sK4) X0]
  have l4 : ∀ sK2 sK0 sK1 sK4 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK4))) := by
    intro sK2 sK0 sK1 sK4 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK1 ◇ sK4)) sK2]
    conv => enter [1]; rw [h39 (sK0 ◇ (sK1 ◇ sK4)) X0]
  have l5 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ sK4) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l2 sK3 sK4 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK4]
  have l6 : ∀ sK2 sK0 sK1 sK4 X0 X1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK4)))) := by
    intro sK2 sK0 sK1 sK4 X0 X1
    conv => enter [1]; rw [l4 sK2 sK0 sK1 sK4 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK4))]
  have l7 : ∀ sK2 sK0 sK1 sK4 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4)))) := by
    intro sK2 sK0 sK1 sK4 X0
    conv => enter [1]; rw [l6 sK2 sK0 sK1 sK4 X0 sK2]
  have l8 : ∀ sK3 sK4 X0 : G, (sK3 ◇ sK4) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l5 sK3 sK4 X0 sK3]
  have l9 : ∀ sK2 sK0 sK1 sK4 sK5 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) = (sK5 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4)))) := by
    intro sK2 sK0 sK1 sK4 sK5
    conv => enter [1]; rw [l7 sK2 sK0 sK1 sK4 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4)))]
    conv => enter [1]; rw [h39 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) sK5]
  have l10 : ∀ sK3 sK4 sK0 sK1 : G, (sK3 ◇ sK4) = (sK0 ◇ (sK1 ◇ sK4)) := by
    intro sK3 sK4 sK0 sK1
    conv => enter [1]; rw [l8 sK3 sK4 (sK3 ◇ sK4)]
    conv => enter [1]; rw [← l1 sK0 sK1 sK4 sK3]
  have l11 : ∀ sK2 sK0 sK1 sK4 sK3 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← h39 (sK0 ◇ (sK1 ◇ sK4)) sK2]
    conv => enter [1, 1]; rw [← l10 sK3 sK4 sK0 sK1]
    conv => enter [1, 2]; rw [← l10 sK3 sK4 sK0 sK1]
  have l12 : ∀ sK0 sK1 sK4 sK2 : G, (sK0 ◇ (sK1 ◇ sK4)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) := by
    intro sK0 sK1 sK4 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK4 (sK0 ◇ sK4) sK0]
    conv => enter [1]; rw [← l11 sK2 sK0 sK1 sK4 sK0]
  have l13 : ∀ sK3 sK4 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) := by
    intro sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [l10 sK3 sK4 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1 sK4 sK2]
  intro x y z w u v
  conv => enter [1]; rw [l13 x y w u v]
  conv => enter [1]; rw [l9 w u v y z]

@[equational_result]
theorem Equation42400_implies_Equation39 (G : Type*) [Magma G] (h42400 : Equation42400 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42400 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42400 X2 X1 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation41934 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41934 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h39 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 sK1]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l5 sK0 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l7 sK0 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l8 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_41934_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41934 : Equation41934 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41934 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41934 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l4 X0 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation39_4512_implies_Equation42231 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42231 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  have l1 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l0 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0 sK2]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [l5 z y]

@[equational_result]
theorem Equation42231_implies_Equation39 (G : Type*) [Magma G] (h42231 : Equation42231 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42231 X0 X1 X0]
    conv => enter [1]; rw [← h42231 X3 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation41937 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41937 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK0) sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [l7 z y]

@[equational_result]
theorem Equation41937_implies_Equation39 (G : Type*) [Magma G] (h41937 : Equation41937 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41937 X0 X1 X0]
    conv => enter [1]; rw [← h41937 X3 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42227 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42227 G := by
  have l0 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h39 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0 sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← h39 y x]
  conv => enter [1]; rw [l3 y z]

@[equational_result]
theorem Equation42227_implies_Equation39 (G : Type*) [Magma G] (h42227 : Equation42227 G) : Equation39 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ sK0) := by
    intro sK0 X1
    conv => enter [1]; rw [h42227 sK0 sK0 sK0]
    conv => enter [1]; rw [← h42227 X1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation39_4512_implies_Equation42235 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42235 G := by
  have l0 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 sK0]
  have l1 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK2]
    conv => enter [1]; rw [h39 sK3 X0]
  have l2 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l3 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK3 X0 sK2]
  have l4 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l3 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1]
  have l5 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l3 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [l5 w y z]

@[equational_result]
theorem Equation42235_implies_Equation39 (G : Type*) [Magma G] (h42235 : Equation42235 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42235 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42235 X4 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation41945 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41945 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h39 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l0 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0 sK1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l3 sK1 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [← h39 y x]
  conv => enter [1]; rw [l6 y z]
  conv => enter [1]; rw [l5 z y]

@[equational_result]
theorem Equation41945_implies_Equation39 (G : Type*) [Magma G] (h41945 : Equation41945 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41945 X0 X1 X0]
    conv => enter [1]; rw [← h41945 X3 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42214 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42214 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK2]
    conv => enter [1]; rw [h39 sK1 X0]
  have l2 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l2 sK2 sK1 X0 sK2]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l8 z y]

@[equational_result]
theorem Equation42214_implies_Equation39 (G : Type*) [Magma G] (h42214 : Equation42214 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42214 X0 X1 X0]
    conv => enter [1]; rw [← h42214 X3 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42250 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42250 G := by
  have l0 : ∀ sK0 sK3 X0 : G, (sK0 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK0]
    conv => enter [1]; rw [h39 sK3 X0]
  have l1 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK1 ◇ sK3)) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [← h39 (sK1 ◇ sK3) sK2]
    conv => enter [1]; rw [h39 (sK1 ◇ sK3) X0]
  have l2 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [l0 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l3 : ∀ sK2 sK1 sK3 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK3)]
  have l4 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK3 X0 sK2]
  have l5 : ∀ sK0 sK3 X0 : G, (sK0 ◇ sK3) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l2 sK0 sK3 X0 sK0]
  have l6 : ∀ sK1 sK3 X0 : G, (sK1 ◇ sK3) = (X0 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 X0
    conv => enter [1]; rw [l5 sK1 sK3 X0]
  have l7 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [l4 sK2 sK1 sK3 sK1]
    conv => enter [1, 2]; rw [l4 sK2 sK1 sK3 sK1]
  have l8 : ∀ sK1 sK3 sK2 : G, (sK1 ◇ sK3) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK2
    conv => enter [1]; rw [l6 sK1 sK3 (sK1 ◇ sK3)]
    conv => enter [1]; rw [h39 (sK1 ◇ sK3) sK2]
  intro x y z w
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [l8 z y w]
  conv => enter [1]; rw [l7 w z y]

@[equational_result]
theorem Equation42250_implies_Equation39 (G : Type*) [Magma G] (h42250 : Equation42250 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42250 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42250 X4 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation41949 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41949 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [l8 z y]

@[equational_result]
theorem Equation41949_implies_Equation39 (G : Type*) [Magma G] (h41949 : Equation41949 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X1) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41949 X0 X1 X0]
    conv => enter [1]; rw [← h41949 X3 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42210 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42210 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h39 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← h39 y x]
  conv => enter [1]; rw [l6 y z]

@[equational_result]
theorem Equation42210_implies_Equation39 (G : Type*) [Magma G] (h42210 : Equation42210 G) : Equation39 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ sK0) := by
    intro sK0 X1
    conv => enter [1]; rw [h42210 sK0 sK0 sK0]
    conv => enter [1]; rw [← h42210 X1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation39_4512_implies_Equation42255 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42255 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 sK3 X0 : G, (sK0 ◇ sK3) = (X0 ◇ sK3) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [← h39 sK3 sK0]
    conv => enter [1]; rw [h39 sK3 X0]
  have l2 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK0 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l3 : ∀ sK0 sK3 X0 : G, (sK0 ◇ sK3) = (X0 ◇ (sK0 ◇ sK3)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l2 sK0 sK3 X0 sK0]
  have l4 : ∀ sK2 sK3 X0 : G, (sK2 ◇ sK3) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l3 sK2 sK3 X0]
  have l5 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK3) sK1]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK2]
  have l6 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l4 sK2 sK3 sK2]
    conv => enter [1]; rw [l5 sK2 sK3 sK1]
  have l7 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK3) sK1]
    conv => enter [1, 2]; rw [l6 sK2 sK3 sK1]
  have l8 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l4 sK2 sK3 sK2]
    conv => enter [1]; rw [l7 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y w]
  conv => enter [1]; rw [l8 w y z]

@[equational_result]
theorem Equation42255_implies_Equation39 (G : Type*) [Magma G] (h42255 : Equation42255 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42255 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42255 X4 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation41927 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41927 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 sK0 sK1]
    conv => enter [1]; rw [h39 sK0 X0]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK0) X0]
  have l4 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0 sK1]
  have l6 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l5 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK2]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l6 sK1 sK0 sK2]
  have l8 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l8 sK1 sK0 sK2]
  have l10 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41927_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41927 : Equation41927 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41927 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41927 X0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41927 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l4 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h41927 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41927 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ sK0))]
  have l6 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [← l4 X0 X1 X3 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41927 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0 X0]
    conv => enter [1, 2]; rw [← l5 X0 sK0 (X0 ◇ sK0)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41927 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l6 X3 X0 X1 X0]
    conv => enter [1]; rw [← l1 X0 X3 X1 X0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l8 X0 sK0]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ sK0)]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 sK0 X0 sK0]
    conv => enter [1]; rw [← l11 X0 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 X0 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l15 y x]

theorem Equation39_4512_implies_Equation41953 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation41953 G := by
  have l0 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ sK1) = (sK3 ◇ sK1) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h39 (sK3 ◇ sK1) sK2]
    conv => enter [1, 1]; rw [l0 sK3 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK3 sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK2 sK3 sK1 X0 sK0 : G, (sK2 ◇ (sK3 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK1 X0 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK3 ◇ sK1)) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK2 sK3 sK1 sK0]
  have l7 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK3 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l3 sK2 sK3 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l6 sK2 sK1 sK2 sK3]
  have l8 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK3]
    conv => enter [1]; rw [l7 sK2 sK3 sK1]
  have l9 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK3 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l3 sK2 sK3 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l8 sK2 sK1 sK2 sK3]
  have l10 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK3]
    conv => enter [1]; rw [l9 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

@[equational_result]
theorem Equation41953_implies_Equation39 (G : Type*) [Magma G] (h41953 : Equation41953 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41953 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41953 X4 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42218 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42218 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h39 sK2 sK3]
    conv => enter [1]; rw [h39 sK2 sK0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK3 sK2 X0 : G, (sK3 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK3]
    conv => enter [1]; rw [h39 sK2 X0]
  have l3 : ∀ sK3 sK2 X0 X1 : G, (sK3 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [l2 sK3 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK3 sK2 X0 : G, (sK3 ◇ sK2) = (X0 ◇ (sK3 ◇ sK2)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [l3 sK3 sK2 X0 sK3]
  have l5 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l1 sK2 (sK3 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [l4 sK3 sK2 sK2]
  have l6 : ∀ sK3 sK2 sK1 : G, (sK3 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2 sK1
    conv => enter [1]; rw [l4 sK3 sK2 sK2]
    conv => enter [1]; rw [l5 sK2 sK3 sK1]
  have l7 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l1 sK2 (sK3 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [l6 sK3 sK2 sK1]
  have l8 : ∀ sK3 sK2 sK1 : G, (sK3 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2 sK1
    conv => enter [1]; rw [l4 sK3 sK2 sK2]
    conv => enter [1]; rw [l7 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [l8 w y z]

@[equational_result]
theorem Equation42218_implies_Equation39 (G : Type*) [Magma G] (h42218 : Equation42218 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42218 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42218 X4 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation39_4512_implies_Equation42193 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42193 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h39 sK2 sK1]
    conv => enter [1]; rw [h39 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h39 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [← h39 sK2 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l5 sK1 sK2]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l7 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_42193_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42193 : Equation42193 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42193 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42193 (X0 ◇ (X1 ◇ X1)) (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 2, 2]; rw [← h42193 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42193 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42193 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ X1))]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42193 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ (X1 ◇ X1))]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X0))]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X0 ◇ (X1 ◇ X1))]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1)))]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2]; rw [← l5 (sK0 ◇ sK0) X0 sK0]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l9 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X1 ◇ X1))]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42193 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK0 X0 X1]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l12 X2 X0 X1]
    conv => enter [1, 2]; rw [← h42193 X0 X1 X1]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l16 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ X1)) = ((sK1 ◇ sK0) ◇ X1) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← l2 sK1 sK0 X0]
  have l17 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← l16 X0 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 ((sK1 ◇ sK0) ◇ sK0) X1]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← l13 (sK1 ◇ sK0) sK0 sK0]
  have l19 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X1)))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l17 sK1 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X1]
  have l20 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ sK0) ◇ X1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X1))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l19 sK1 sK0 X1 sK1]
    conv => enter [1]; rw [l14 sK1 (sK1 ◇ sK0) (sK0 ◇ X1)]
  have l21 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ sK0) ◇ X1) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l20 sK1 sK0 X1]
    conv => enter [1]; rw [l14 (sK1 ◇ sK0) sK0 X1]
  have l22 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l21 sK1 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 sK0 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l23 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l24 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l29 sK1 sK0]
  have l31 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0 sK0]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l31 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 (sK0 ◇ sK0)]
  have l33 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h42193 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← l31 sK0]
  have l34 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [h42193 X1 sK0 X1]
    conv => enter [1]; rw [← l33 X1 sK0 X1]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l36 sK1 sK0]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK0]
    conv => enter [1]; rw [← l38 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l39 x y]

theorem Equation39_4512_implies_Equation42245 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42245 G := by
  have l0 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h39 (sK3 ◇ sK3) sK2]
    conv => enter [1]; rw [h39 (sK3 ◇ sK3) X0]
  have l1 : ∀ sK3 X0 X1 : G, (sK3 ◇ sK3) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [h39 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK3]
  have l2 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l0 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ sK3)]
  have l3 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK3 X0 sK2]
  have l4 : ∀ sK3 X0 : G, (sK3 ◇ sK3) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK3 X0
    conv => enter [1]; rw [l1 sK3 X0 sK3]
  have l5 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l3 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1]
  have l6 : ∀ sK3 sK2 : G, (sK3 ◇ sK3) = (sK2 ◇ (sK3 ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [l4 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [h39 (sK3 ◇ sK3) sK2]
  intro x y z w
  conv => enter [1]; rw [← h39 y x]
  conv => enter [1]; rw [l6 y w]
  conv => enter [1]; rw [l5 w y z]

@[equational_result]
theorem Equation42245_implies_Equation39 (G : Type*) [Magma G] (h42245 : Equation42245 G) : Equation39 G := by
  have l0 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ sK0) := by
    intro sK0 X2
    conv => enter [1]; rw [h42245 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h42245 X2 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation39_4512_implies_Equation42201 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42201 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = (sK2 ◇ sK0) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h39 sK0 sK3]
    conv => enter [1]; rw [h39 sK0 sK2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  have l2 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h39 sK0 sK3]
    conv => enter [1]; rw [h39 sK0 X0]
  have l3 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l3 sK3 sK0 X0 sK3]
  have l5 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l1 sK2 (sK3 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [l4 sK3 sK0 sK2]
  have l6 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK3 sK0 sK2]
    conv => enter [1]; rw [l5 sK2 sK3 sK0 sK1]
  have l7 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l1 sK2 (sK3 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [l6 sK3 sK0 sK1 sK2]
  have l8 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK3 sK0 sK2]
    conv => enter [1]; rw [l7 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [l8 w y z x]

theorem Equation4512_42201_implies_Equation39 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42201 : Equation42201 G) : Equation39 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X3 X4 X0 X5 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X5 ◇ X1)))) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := by
    intro X3 X4 X0 X5 X1 X2
    conv => enter [1]; rw [h42201 X3 (X4 ◇ (X0 ◇ (X5 ◇ X1))) X2 X4]
    conv => enter [1, 2, 2, 2]; rw [← h42201 X0 X1 X4 X5]
  have l2 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ X0) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h42201 sK1 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42201 (sK1 ◇ sK0) X0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 X0 sK1 sK0]
  have l4 : ∀ X3 X4 X0 X5 X1 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X5 ◇ X1)))) = (X3 ◇ X1) := by
    intro X3 X4 X0 X5 X1
    conv => enter [1]; rw [l1 X3 X4 X0 X5 X1 X3]
    conv => enter [1]; rw [← h42201 X3 X1 X3 X0]
  have l5 : ∀ X0 X2 sK1 sK0 X1 : G, (X0 ◇ X2) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 sK1 sK0 X1
    conv => enter [1]; rw [h42201 X0 X2 (sK1 ◇ sK0) X1]
    conv => enter [1, 2]; rw [l3 sK1 sK0 (X0 ◇ (X1 ◇ X2))]
  have l6 : ∀ X0 X2 sK1 sK0 : G, (X0 ◇ X2) = ((sK1 ◇ sK0) ◇ X2) := by
    intro X0 X2 sK1 sK0
    conv => enter [1]; rw [l5 X0 X2 sK1 sK0 X0]
    conv => enter [1]; rw [l4 (sK1 ◇ sK0) sK1 X0 X0 X2]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l3 sK1 sK0 sK0]
    conv => enter [1]; rw [← l6 X0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x x y]

theorem Equation39_4512_implies_Equation42260 (G : Type*) [Magma G] (h39 : Equation39 G) (h4512 : Equation4512 G) : Equation42260 G := by
  have l0 : ∀ sK0 sK1 sK4 : G, (sK0 ◇ sK1) = (sK4 ◇ sK1) := by
    intro sK0 sK1 sK4
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 sK4]
  have l1 : ∀ sK3 sK4 sK1 sK0 : G, (sK3 ◇ (sK4 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h39 (sK4 ◇ sK1) sK3]
    conv => enter [1, 1]; rw [l0 sK4 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK4 sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  have l3 : ∀ sK3 sK4 sK1 X0 sK0 : G, (sK3 ◇ (sK4 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK1 X0 sK0
    conv => enter [1]; rw [l1 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [h39 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
  have l6 : ∀ sK0 sK1 sK3 sK4 : G, (sK0 ◇ sK1) = (sK3 ◇ (sK4 ◇ sK1)) := by
    intro sK0 sK1 sK3 sK4
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK3 sK4 sK1 sK0]
  have l7 : ∀ sK3 sK4 sK1 sK2 : G, (sK3 ◇ (sK4 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) := by
    intro sK3 sK4 sK1 sK2
    conv => enter [1]; rw [l3 sK3 sK4 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l6 sK3 sK1 sK3 sK4]
  have l8 : ∀ sK0 sK1 sK2 sK3 sK4 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) := by
    intro sK0 sK1 sK2 sK3 sK4
    conv => enter [1]; rw [l6 sK0 sK1 sK3 sK4]
    conv => enter [1]; rw [l7 sK3 sK4 sK1 sK2]
  have l9 : ∀ sK3 sK4 sK1 sK2 : G, (sK3 ◇ (sK4 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK3 sK4 sK1 sK2
    conv => enter [1]; rw [l3 sK3 sK4 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l8 sK3 sK1 sK2 sK3 sK4]
  have l10 : ∀ sK0 sK1 sK2 sK3 sK4 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK0 sK1 sK2 sK3 sK4
    conv => enter [1]; rw [l6 sK0 sK1 sK3 sK4]
    conv => enter [1]; rw [l9 sK3 sK4 sK1 sK2]
  intro x y z w u
  conv => enter [1]; rw [l10 x y z w u]

@[equational_result]
theorem Equation42260_implies_Equation39 (G : Type*) [Magma G] (h42260 : Equation42260 G) : Equation39 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X5 ◇ X1) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h42260 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42260 X5 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

theorem Equation40_4512_implies_Equation3269 (G : Type*) [Magma G] (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation3269 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h40 X0 sK0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h40 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3269_4512_implies_Equation40 (G : Type*) [Magma G] (h3269 : Equation3269 G) (h4512 : Equation4512 G) : Equation40 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3269 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3269 sK0 sK0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3269 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3269 sK1 sK1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3269 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3269 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK1 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation40_4512_implies_Equation3282 (G : Type*) [Magma G] (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation3282 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h40 X0 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [h40 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h40 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h40 sK0 sK1]
    conv => enter [1]; rw [l2 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation3282_implies_Equation40 (G : Type*) [Magma G] (h3282 : Equation3282 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3282 X0 X0]
    conv => enter [1]; rw [← h3282 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation40_4512_implies_Equation3286 (G : Type*) [Magma G] (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation3286 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h40 X0 sK0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2, 2]; rw [h40 sK2 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h40 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK1 sK2 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h40 sK0 sK2]
    conv => enter [1]; rw [l2 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation3286_implies_Equation40 (G : Type*) [Magma G] (h3286 : Equation3286 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3286 X0 X0 X0]
    conv => enter [1]; rw [← h3286 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation40_4512_implies_Equation3294 (G : Type*) [Magma G] (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation3294 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h40 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation3294_implies_Equation40 (G : Type*) [Magma G] (h3294 : Equation3294 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3294 X0 X0 X0]
    conv => enter [1]; rw [← h3294 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation40_4512_implies_Equation3297 (G : Type*) [Magma G] (h40 : Equation40 G) (h4512 : Equation4512 G) : Equation3297 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [h40 X0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 X0 X0 sK0]
    conv => enter [1, 2]; rw [h40 X0 sK0]
  have l2 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l2 sK2 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h40 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation3297_implies_Equation40 (G : Type*) [Magma G] (h3297 : Equation3297 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3297 X0 X0 X0]
    conv => enter [1]; rw [← h3297 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation41_implies_Equation44 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation44 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

@[equational_result]
theorem Equation44_implies_Equation41 (G : Type*) [Magma G] (h44 : Equation44 G) : Equation41 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h44 sK0 sK1 sK2]
    conv => enter [1]; rw [← h44 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

@[equational_result]
theorem Equation41_implies_Equation46 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation46 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation46_implies_Equation41 (G : Type*) [Magma G] (h46 : Equation46 G) : Equation41 G := by
  intro x y z
  conv => enter [1]; rw [h46 x x y z]

end Semigroup5
