import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41692_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41692 : Equation41692 G) : Equation316 G := by
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
  have l3 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h41692 (sK0 ◇ sK0) X1 X2 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l4 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41692 sK1 X1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41692 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 X0]
  have l6 : ∀ X0 X2 sK1 X1 : G, (X0 ◇ X0) = (X2 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [h41692 X0 X2 sK1 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1 sK1]
  have l8 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l4 sK1 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41692 sK0 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 sK0 sK0 sK0]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l7 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l10 sK1 X0]
  have l12 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h41692 X0 (sK1 ◇ sK1) X0 X0]
    conv => enter [1]; rw [← l11 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [l13 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]
  conv => enter [1]; rw [l12 y]

@[equational_result]
theorem Equation316_implies_Equation41694 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41694 G := by
  have l0 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK1]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 sK0 X1]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h316 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 X0 sK0]
    conv => enter [1, 2]; rw [l2 X0 sK0]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l2 sK1 sK2]
    conv => enter [1, 2]; rw [l5 sK2 sK2 sK1]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l5 sK0 sK2 sK1]
    conv => enter [1]; rw [l6 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l7 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_41694_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41694 : Equation41694 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41694 X0 X0 X0]
    conv => enter [1]; rw [← h41694 X1 X0 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l1 X0 sK0]
  have l11 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41694 X1 X1 X2]
    conv => enter [1]; rw [l1 X1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (X2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [← l11 X1 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 sK1]
  have l16 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l15 sK0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [l10 sK0 (sK1 ◇ sK1) sK0]
  have l17 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l16 sK0 X1 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  have l18 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l17 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation316_4512_implies_Equation41695 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41695 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l2 sK0 X2 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 X2 sK0 sK0]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 X2]
    conv => enter [1]; rw [l4 X2 X2 sK0]
  have l11 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK0]
  have l12 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK0 sK0]
  have l13 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l12 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK2 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_41695_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41695 : Equation41695 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41695 X0 X0 X0]
    conv => enter [1]; rw [← h41695 X1 X0 X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l5 X0 sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1, 1]; rw [l5 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l8 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l17 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l16 sK1 X0]
    conv => enter [1, 1]; rw [l5 sK1 sK0]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41695 X0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK1 sK0]
  have l19 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l18 X0 X0 sK1]
    conv => enter [1]; rw [← l17 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l19 X0 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l21 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l20 X0 X0 sK1]
    conv => enter [1]; rw [← l15 sK1 X0]
  have l22 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l22 sK1]
  intro x y
  conv => enter [1]; rw [l23 x y]

theorem Equation316_4512_implies_Equation41696 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41696 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 X2 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 X2]
    conv => enter [1]; rw [l4 X2 X2 sK1]
  have l11 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK1]
  have l12 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK1 sK1]
  have l13 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l12 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l13 sK1 sK3 (sK2 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l14 x y z w]

theorem Equation4512_41696_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41696 : Equation41696 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41696 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41696 X0 X1 X1 X1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h41696 X0 X1 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 sK1]
  have l15 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l14 X0 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l10 sK0 (sK1 ◇ sK1) X0]
  have l16 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l15 X0 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 X0]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 X0]
    conv => enter [1, 2]; rw [← l11 sK0 X0]
  have l18 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l17 sK1 X1 sK0]
  have l19 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l18 sK0 X1 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation316_4512_implies_Equation41698 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41698 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l2 sK0 X2 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 X2 sK0 sK0]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 X2]
    conv => enter [1]; rw [l4 X2 X2 sK0]
  have l11 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK0]
  have l12 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK0 sK0]
  have l13 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l12 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1, 2]; rw [l13 sK0 sK2 sK1]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l15 x y z]

theorem Equation4512_41698_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41698 : Equation41698 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41698 X0 X0 X0]
    conv => enter [1]; rw [← h41698 X1 X0 X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l6 sK1 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l5 X0 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1, 1]; rw [l5 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41698 X0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1]
  have l18 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l17 X0 sK1]
    conv => enter [1, 2]; rw [l10 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l19 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l18 X0 sK1 X0]
    conv => enter [1, 2]; rw [← l16 sK1 X0]
  have l20 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l19 X0 sK1]
    conv => enter [1]; rw [← l9 sK1]
  have l21 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l21 sK1]
  intro x y
  conv => enter [1]; rw [l22 x y]

@[equational_result]
theorem Equation316_implies_Equation41699 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41699 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h316 sK2 sK2]
    conv => enter [1]; rw [h316 sK2 X0]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l0 sK2 X0]
    conv => enter [1, 2]; rw [h316 X0 sK2]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h316 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 X0]
    conv => enter [1, 2]; rw [← h316 sK2 sK2]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [h316 sK0 sK2]
    conv => enter [1]; rw [← h316 sK2 sK2]
  have l4 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [h316 sK2 sK2]
    conv => enter [1, 2]; rw [h316 sK2 sK2]
  have l5 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [l4 sK2]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_41699_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41699 : Equation41699 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41699 X0 X0 X0]
    conv => enter [1]; rw [← h41699 X1 X0 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l6 sK1 X1 X2]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l8 sK1 sK1]
  have l11 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h41699 X1 X1 X2]
    conv => enter [1]; rw [l5 X1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l11 X1 sK0 sK0]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l14 sK0 X1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation316_4512_implies_Equation41700 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41700 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 X2 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 X2]
    conv => enter [1]; rw [l4 X2 X2 sK1]
  have l11 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK1]
  have l12 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK1 sK1]
  have l13 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l12 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK3]
    conv => enter [1, 2]; rw [l13 sK1 sK3 sK0]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l14 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]

theorem Equation4512_41700_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41700 : Equation41700 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41700 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41700 X0 X1 X1 X1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l1 X0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h41700 X0 X1 X2 X2]
    conv => enter [1, 2, 2, 2]; rw [l1 X2 sK1]
  have l15 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l14 X0 X1 X0 sK1]
    conv => enter [1, 2]; rw [l10 X0 (sK1 ◇ sK1) sK0]
  have l16 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l15 X0 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 X0]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 X0]
    conv => enter [1, 2]; rw [← l11 sK0 X0]
  have l18 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l17 sK1 X1 sK0]
  have l19 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l18 sK0 X1 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation316_4512_implies_Equation41702 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41702 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 X2 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 X2]
    conv => enter [1]; rw [l4 X2 X2 sK1]
  have l11 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK1]
  have l12 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK1 sK1]
  have l13 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l12 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l13 sK1 sK3 (sK0 ◇ sK2)]
  intro x y z w
  conv => enter [1]; rw [l14 x y z w]

theorem Equation4512_41702_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41702 : Equation41702 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41702 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41702 X0 X1 X1 X1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l6 sK1 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l5 X0 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1, 1]; rw [l5 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l19 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h41702 X0 (sK0 ◇ sK0) X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK1 sK0]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l19 X0 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [l10 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l21 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l20 X0 sK0 sK1]
    conv => enter [1]; rw [l10 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l22 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l21 X0 X0 sK1]
    conv => enter [1]; rw [← l18 sK1 X0]
  have l23 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l23 sK1]
  intro x y
  conv => enter [1]; rw [l24 x y]

theorem Equation316_4512_implies_Equation41703 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41703 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 X2 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 X2]
    conv => enter [1]; rw [l4 X2 X2 sK1]
  have l11 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK1]
  have l12 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK1 sK1]
  have l13 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l12 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l13 sK1 sK3 (sK0 ◇ sK3)]
  intro x y z w
  conv => enter [1]; rw [l14 x y z w]

theorem Equation4512_41703_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41703 : Equation41703 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41703 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41703 X0 X1 X1 X1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l6 sK1 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l5 X0 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1, 1]; rw [l5 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l19 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41703 X0 X1 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK1 sK0]
  have l20 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l19 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [l10 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l21 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l20 X0 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l18 sK1 X0]
  have l22 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l21 sK1 X1 sK1]
  have l23 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l22 sK1 X1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l9 sK1]
  intro x y
  conv => enter [1]; rw [l24 x y]

@[equational_result]
theorem Equation316_implies_Equation41704 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41704 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h316 sK1 sK1]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK1]
  have l3 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l2 sK1 X1 sK1]
  have l4 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l3 sK1 X1]
    conv => enter [1, 2]; rw [← l1 sK1]
  have l5 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l6 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1, 2]; rw [l0 sK0 sK3]
    conv => enter [1, 2]; rw [l5 sK3 sK3 sK0]
  have l7 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK3 sK0]
    conv => enter [1]; rw [l6 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1, 2]; rw [l7 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_41704_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41704 : Equation41704 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41704 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41704 X0 X1 X1 X1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l1 X0 sK0]
  have l11 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41704 sK0 X1 X2 X3]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (X2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [l11 sK0 X1 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [l1 sK0 sK1]
  have l16 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l15 sK0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [l10 sK0 (sK1 ◇ sK1) sK0]
  have l17 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l16 sK0 X1 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  have l18 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l17 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation316_4512_implies_Equation41705 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41705 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK2 : G, (X1 ◇ X1) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK2]
  have l3 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X2
    conv => enter [1]; rw [l2 sK2 X2 sK2]
  have l4 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK2 X2
    conv => enter [1]; rw [l7 sK2 sK2 sK2]
    conv => enter [1]; rw [← l6 X2 sK2 sK2]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X2
    conv => enter [1]; rw [l8 sK2 X2]
    conv => enter [1]; rw [l4 X2 X2 sK2]
  have l11 : ∀ X0 X2 sK2 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK2 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK2]
  have l12 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = ((X0 ◇ X0) ◇ X2) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l10 sK2 (sK2 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK2 sK2]
  have l13 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l12 sK2 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3]
    conv => enter [1, 2]; rw [l13 sK2 sK4 (sK1 ◇ sK0)]
  intro x y z w u
  conv => enter [1]; rw [l14 x y z w u]

theorem Equation4512_41705_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41705 : Equation41705 G) : Equation316 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41705 X1 X2 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41705 X0 X1 X1 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41705 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h41705 X1 X0 X0 X0 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← l3 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l6 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation316_implies_Equation41712 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41712 G := by
  have l0 : ∀ X1 sK2 : G, (X1 ◇ (X1 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK2
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK2]
  have l1 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 sK1 X1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h316 sK1 sK2]
    conv => enter [1, 2]; rw [l2 sK2 sK1]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l1 X0 sK1]
    conv => enter [1, 2]; rw [l2 X0 sK1]
  have l5 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK2]
  have l6 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK3]
    conv => enter [1, 2]; rw [l5 sK1 sK0 sK2]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l6 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

theorem Equation4512_41712_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41712 : Equation41712 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41712 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41712 X0 X1 X1 X1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41712 X1 X2 (X1 ◇ (X2 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X1 ◇ (X2 ◇ X2)) X0]
  have l3 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l1 sK1 sK1]
  have l5 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l3 sK1 X2 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l4 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [l6 y]

@[equational_result]
theorem Equation316_implies_Equation41718 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41718 G := by
  have l0 : ∀ X1 sK3 : G, (X1 ◇ (X1 ◇ X1)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro X1 sK3
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK3]
  have l1 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 sK1 X1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l3 : ∀ sK1 sK3 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3
    conv => enter [1]; rw [h316 sK1 sK3]
    conv => enter [1, 2]; rw [l2 sK3 sK1]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l1 X0 sK1]
    conv => enter [1, 2]; rw [l2 X0 sK1]
  have l5 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK3]
  have l6 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK3]
    conv => enter [1, 2]; rw [l5 sK1 sK0 sK3]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1, 2]; rw [l6 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

theorem Equation4512_41718_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41718 : Equation41718 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l1 sK1]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41718 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41718 X0 X1 X1 X1]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l4 (sK1 ◇ sK1) X0]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h41718 X1 X2 X3 (X3 ◇ X3)]
    conv => enter [1, 2, 2]; rw [l4 (X3 ◇ X3) X0]
  have l7 : ∀ X1 X2 X3 sK1 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (sK1 ◇ sK1))) := by
    intro X1 X2 X3 sK1
    conv => enter [1]; rw [l6 X1 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [l4 X1 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l5 sK1 sK1]
  have l9 : ∀ sK1 X2 X3 : G, (sK1 ◇ sK1) = (X2 ◇ (X3 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [l7 sK1 X2 X3 sK1]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l4 (sK1 ◇ sK1) sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation316_4512_implies_Equation41719 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41719 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h4512 sK3 sK0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h316 (sK3 ◇ sK0) sK1]
  have l5 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK1]
    conv => enter [1]; rw [← l4 sK3 sK0 sK1]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l5 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

theorem Equation4512_41719_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41719 : Equation41719 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41719 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41719 X0 X1 X1 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l6 sK1 X1 X2]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l8 sK1 sK1]
  have l11 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h41719 sK0 X1 X2 X3]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l11 sK0 X1 sK0 sK0]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l14 sK0 X1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation316_4512_implies_Equation41722 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41722 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 X2 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 X2]
    conv => enter [1]; rw [l4 X2 X2 sK1]
  have l11 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK1]
  have l12 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK1 sK1]
  have l13 : ∀ X0 X2 sK1 : G, (X0 ◇ (X0 ◇ X2)) = (sK1 ◇ sK1) := by
    intro X0 X2 sK1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [← l12 sK1 X0 X2]
  have l14 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK3]
    conv => enter [1, 2]; rw [← l13 sK0 sK2 sK1]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l14 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]

theorem Equation4512_41722_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41722 : Equation41722 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41722 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41722 X0 X1 X1 X1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41722 X1 X2 (X1 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2]; rw [l0 (X1 ◇ (X1 ◇ X2)) X0]
  have l3 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l1 sK1 sK1]
  have l5 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l3 sK1 X2 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l4 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [l6 y]

theorem Equation316_4512_implies_Equation41723 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41723 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 X2 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 X2]
    conv => enter [1]; rw [l4 X2 X2 sK1]
  have l11 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK1]
  have l12 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK1 sK1]
  have l13 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l12 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK3]
    conv => enter [1, 2]; rw [l13 sK1 sK0 sK3]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l14 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]

theorem Equation4512_41723_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41723 : Equation41723 G) : Equation316 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l3 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l5 sK1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41723 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41723 X0 X1 X1 X1]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l7 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 (sK1 ◇ sK1) X0]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l4 sK1]
    conv => enter [1]; rw [l9 sK1 X0]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l10 sK1 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK1]
    conv => enter [1, 2]; rw [l7 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 (sK1 ◇ sK1) sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l4 sK1]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l15 sK1 sK0]
    conv => enter [1, 2, 1]; rw [l7 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1, 1]; rw [l7 sK1 sK0]
  have l23 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h41723 X0 X1 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l22 sK1 sK0]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l23 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l21 sK0 X0]
  have l25 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l24 sK1 X1 sK0]
  have l26 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l25 sK0 X1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l20 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l27 x y]

@[equational_result]
theorem Equation316_implies_Equation41724 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41724 G := by
  have l0 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK0]
  have l1 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 sK1 X1]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [← l1 X1 sK1]
    conv => enter [1, 2]; rw [h316 X1 sK0]
  have l3 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l2 sK1 X1 sK1]
    conv => enter [1, 2]; rw [← h316 sK1 sK1]
  have l4 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK3]
    conv => enter [1, 2]; rw [h316 sK1 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l4 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_41724_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41724 : Equation41724 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41724 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41724 X0 X1 X1 X1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41724 X1 X2 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [l0 (X1 ◇ (X1 ◇ X1)) X0]
  have l3 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l2 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← l1 sK1 sK1]
  have l5 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l3 sK1 X2 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l4 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [l6 y]

theorem Equation316_4512_implies_Equation41725 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41725 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK2 : G, (X1 ◇ X1) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK2]
  have l3 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X2
    conv => enter [1]; rw [l2 sK2 X2 sK2]
  have l4 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK2 X2
    conv => enter [1]; rw [l7 sK2 sK2 sK2]
    conv => enter [1]; rw [← l6 X2 sK2 sK2]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X2
    conv => enter [1]; rw [l8 sK2 X2]
    conv => enter [1]; rw [l4 X2 X2 sK2]
  have l11 : ∀ X0 X2 sK2 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK2 ◇ sK2) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK2]
  have l12 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = ((X0 ◇ X0) ◇ X2) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l10 sK2 (sK2 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK2 sK2]
  have l13 : ∀ sK2 X0 X2 : G, (sK2 ◇ sK2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK2 X0 X2
    conv => enter [1]; rw [l12 sK2 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK4]
    conv => enter [1, 2]; rw [l13 sK2 sK1 sK0]
  have l15 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3]
    conv => enter [1, 2]; rw [l14 sK2 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l15 x y z w u]

theorem Equation4512_41725_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41725 : Equation41725 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41725 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h41725 X1 X0 X0 X0 X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41725 X0 X1 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1, 2]; rw [l5 (X0 ◇ (X0 ◇ X0)) sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l9 sK1 X1 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l14 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l12 sK0 X1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation316_implies_Equation41730 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41730 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK2 X0]
  have l1 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h316 sK2 sK2]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK2]
  have l3 : ∀ sK2 X1 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1
    conv => enter [1]; rw [l2 sK2 X1 sK2]
  have l4 : ∀ sK2 X1 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X1
    conv => enter [1]; rw [l3 sK2 X1]
    conv => enter [1, 2]; rw [← l1 sK2]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK1]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  have l6 : ∀ sK2 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK4]
    conv => enter [1, 2]; rw [l5 sK2 sK1 sK0]
  have l7 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK3]
    conv => enter [1, 2]; rw [l6 sK2 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u]

theorem Equation4512_41730_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41730 : Equation41730 G) : Equation316 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41730 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h41730 X1 X0 X0 X0 X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41730 X0 X1 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1, 2]; rw [l5 (X0 ◇ (X0 ◇ X0)) sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l9 sK1 X1 sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l14 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l12 sK0 X1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation325_4512_implies_Equation3318 (G : Type*) [Magma G] (h325 : Equation325 G) (h4512 : Equation4512 G) : Equation3318 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h325 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h325 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK0)) = (((sK0 ◇ sK1) ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 ((sK0 ◇ sK1) ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 ((sK1 ◇ sK0) ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 (sK1 ◇ sK0)]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h325 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 sK1 sK0]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 (sK1 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation3318_4512_implies_Equation325 (G : Type*) [Magma G] (h3318 : Equation3318 G) (h4512 : Equation4512 G) : Equation325 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h3318 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h3318 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK1 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3318 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3318 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3318 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l12 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation325_implies_Equation41772 (G : Type*) [Magma G] (h325 : Equation325 G) : Equation41772 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 sK1 sK0]
    conv => enter [1, 2]; rw [h325 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_41772_implies_Equation325 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41772 : Equation41772 G) : Equation325 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41772 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41772 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41772 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))]
  have l8 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK1]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l5 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41772 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l8 X0 X1 X2]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK1 ◇ sK0)]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1, 2]; rw [← l10 X1 X2 X0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l15 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation325_4512_implies_Equation41779 (G : Type*) [Magma G] (h325 : Equation325 G) (h4512 : Equation4512 G) : Equation41779 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h325 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [← h325 (sK0 ◇ sK1) sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation4512_41779_implies_Equation325 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41779 : Equation41779 G) : Equation325 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41779 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41779 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41779 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l4 sK0 sK1]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK0 ◇ sK1) ◇ sK1) X0]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK1 ◇ sK0) ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41779 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41779 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l12 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1, 2]; rw [← l23 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41779 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l30 x y]

theorem Equation325_4512_implies_Equation41782 (G : Type*) [Magma G] (h325 : Equation325 G) (h4512 : Equation4512 G) : Equation41782 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h325 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h325 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_41782_implies_Equation325 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41782 : Equation41782 G) : Equation325 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41782 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41782 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41782 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l19 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ sK1)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41782 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l13 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 (sK0 ◇ sK1)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l6 sK0 sK1 X0]
    conv => enter [1]; rw [l24 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [l6 sK0 sK1 X0]
  have l26 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41782 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l24 sK0 sK1 X0]
  have l27 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l26 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l24 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l27 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l27 (sK1 ◇ sK0) sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1 (sK1 ◇ sK0)]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41782 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l38 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l16 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK1)]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l45 x y]

@[equational_result]
theorem Equation327_implies_Equation3317 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3317 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (x ◇ z)]

theorem Equation3317_4512_implies_Equation327 (G : Type*) [Magma G] (h3317 : Equation3317 G) (h4512 : Equation4512 G) : Equation327 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h3317 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3317 X0 X1 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [← l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3317 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation327_implies_Equation3320 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3320 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (y ◇ z)]

theorem Equation3320_4512_implies_Equation327 (G : Type*) [Magma G] (h3320 : Equation3320 G) (h4512 : Equation4512 G) : Equation327 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h3320 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h3320 X0 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [← l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3320 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← l4 (sK0 ◇ sK1) sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation327_implies_Equation3321 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3321 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (z ◇ x)]

theorem Equation3321_4512_implies_Equation327 (G : Type*) [Magma G] (h3321 : Equation3321 G) (h4512 : Equation4512 G) : Equation327 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3321 X0 X1 X2]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h3321 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h3321 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← l1 X1 X2 X3 X0]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 (X2 ◇ X0) X3]
    conv => enter [1]; rw [← l6 X0 X1 X3 X2]
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3321 X0 X1 X0]
    conv => enter [1]; rw [l7 X0 X1 X0 X3]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3321 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 (sK0 ◇ sK1) X0 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation327_implies_Equation3324 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation3324 G := by
  intro x y z w
  conv => enter [1]; rw [h327 x y (z ◇ w)]

@[equational_result]
theorem Equation3324_implies_Equation327 (G : Type*) [Magma G] (h3324 : Equation3324 G) : Equation327 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h3324 X2 X0 X1 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h3324 X0 X1 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation327_implies_Equation41771 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41771 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (x ◇ (x ◇ z))]

theorem Equation4512_41771_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41771 : Equation41771 G) : Equation327 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41771 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X2))) X3]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X2)) X3]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X2) X3]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l4 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41771 X0 X1 (X0 ◇ X3)]
    conv => enter [1]; rw [← l3 X0 X1 X3 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation327_implies_Equation41774 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41774 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (x ◇ (y ◇ z))]

theorem Equation4512_41774_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41774 : Equation41774 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41774 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ X0))]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ X1) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0) X1]
  have l3 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 X1]
  have l4 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l3 sK0 sK1 X1 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation327_implies_Equation41775 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41775 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (x ◇ (z ◇ x))]

theorem Equation4512_41775_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41775 : Equation41775 G) : Equation327 G := by
  have l0 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ X0) ◇ X1) = ((sK1 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h41775 (sK1 ◇ X0) X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h41775 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41775 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (X0 ◇ sK0))]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41775 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (X0 ◇ sK1))]
  have l4 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l0 sK1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK1 X0 (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l5 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l4 sK1 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l6 : ∀ sK1 X0 X1 : G, ((sK1 ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l5 sK1 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l1 X0 X1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 X0 X1]
    conv => enter [1]; rw [l6 sK1 X0 X1]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (X0 ◇ (X1 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 sK1]
  have l9 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (X0 ◇ sK1)) ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ (X0 ◇ sK1)) X1]
    conv => enter [1, 1]; rw [← l3 sK1 sK2 X0]
  have l10 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ ((X0 ◇ sK1) ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l9 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (X0 ◇ sK1) X1]
  have l11 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l7 sK1 X0 X1]
  have l12 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ X1)))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l10 sK1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 sK1 X1]
  have l13 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l11 sK1 sK2 sK1 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l12 sK1 sK2 X1 sK1]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l13 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 sK2 sK0]
  have l17 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l18 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l17 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 sK2 X0]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 sK0]
    conv => enter [1]; rw [← l18 sK0 sK1 X0 sK0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

@[equational_result]
theorem Equation327_implies_Equation41777 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41777 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (x ◇ (z ◇ z))]

theorem Equation4512_41777_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41777 : Equation41777 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h41777 X0 X2 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41777 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h41777 X1 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41777 (X0 ◇ X0) X1 X0]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h41777 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41777 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (X0 ◇ X0))]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41777 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (X0 ◇ X0))]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l7 : ∀ X0 X2 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X2
    conv => enter [1]; rw [l1 X0 X2 X0]
    conv => enter [1]; rw [← l3 X0 X2 X0 X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l7 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK1 X0]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ (X0 ◇ X0))]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 (X0 ◇ X0)]
  have l17 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l16 sK0 sK1 sK2 X0]
  have l18 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← l17 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l19 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (X0 ◇ X0)) ◇ X1)) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l4 sK0 sK1 X0]
  have l20 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ X1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l19 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 (X0 ◇ X0) X1]
  have l21 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ X1) = ((sK0 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l13 sK0 sK1 ((X0 ◇ X0) ◇ X1)]
  have l22 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ X1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l6 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X0 ◇ sK1))]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l6 sK2 X0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (X0 ◇ (X0 ◇ sK2))]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2 X0]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 sK1 X0]
    conv => enter [1]; rw [← l24 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (X0 ◇ X0)]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l29 sK0 sK1 sK2 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l36 x y z]

@[equational_result]
theorem Equation327_implies_Equation41778 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41778 G := by
  intro x y z w
  conv => enter [1]; rw [h327 x y (x ◇ (z ◇ w))]

theorem Equation4512_41778_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41778 : Equation41778 G) : Equation327 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h41778 X1 X0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41778 X0 X1 X1 X1]
  have l1 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [h41778 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
  have l2 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l3 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l4 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41778 X0 X1 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l3 X0 X1 X4 X0 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l4 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 x y z]

@[equational_result]
theorem Equation327_implies_Equation41781 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41781 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (y ◇ (x ◇ z))]

theorem Equation4512_41781_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41781 : Equation41781 G) : Equation327 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41781 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X2))) X3]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X2)) X3]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l4 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41781 X0 X1 (X0 ◇ X3)]
    conv => enter [1]; rw [← l3 X0 X1 X3 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation327_implies_Equation41784 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41784 G := by
  have l0 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h327 sK1 sK1 sK2]
    conv => enter [1]; rw [h327 sK1 sK1 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h327 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41784_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41784 : Equation41784 G) : Equation327 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41784 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41784 X0 X0 X1]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41784 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X2)) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l6 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41784 X0 X1 (X0 ◇ X3)]
    conv => enter [1]; rw [← l5 X0 X1 X3 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK1) sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation327_implies_Equation41785 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41785 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (y ◇ (z ◇ x))]

theorem Equation4512_41785_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41785 : Equation41785 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41785 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (X0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41785 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (X0 ◇ sK0))]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41785 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ (X0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h41785 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l5 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41785 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 (X0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l9 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h41785 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l11 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l16 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l10 sK0 sK1 sK2 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ sK0)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((X0 ◇ (X1 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ (X1 ◇ sK0)) X2]
    conv => enter [1, 1]; rw [← l10 sK0 sK1 sK2 X0 X1]
  have l19 : ∀ sK0 sK1 sK2 X2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((X1 ◇ sK0) ◇ X2))) := by
    intro sK0 sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [← l18 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ sK0) X2]
  have l20 : ∀ sK0 sK1 sK2 X2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ X2)))) := by
    intro sK0 sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 sK0 X2]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41785 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l12 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2 (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l20 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) X0 X0]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2 X0]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l24 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 sK1 sK2 X0]
  have l27 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l26 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) X1]
  have l28 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l27 sK0 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
  have l29 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l15 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← l28 sK0 sK1 sK2 X1 X0]
  have l30 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [h41785 sK0 X0 X1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 (X0 ◇ (X0 ◇ (X1 ◇ sK0)))]
  have l31 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l16 sK0 sK1 sK2 X0 X0 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2 X0 sK0]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 sK1]
  have l33 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l31 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l29 sK0 sK1 sK2 sK0 X0]
  have l34 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l32 sK0 sK1 sK2]
  have l35 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l34 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l36 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l35 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l37 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l36 sK1 sK2 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l33 sK0 sK1 sK2 X0]
  have l38 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l34 sK1 sK2 sK1]
    conv => enter [1]; rw [← l37 sK1 sK2 X0 sK1]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l38 sK1 sK2 sK0]
  have l40 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l39 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
  have l41 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l40 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l38 sK1 sK2 X0]
  have l42 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l39 sK0 sK1 sK0]
    conv => enter [1]; rw [← l41 sK0 sK1 X0 sK0]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l43 x y z]

@[equational_result]
theorem Equation327_implies_Equation41787 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41787 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (y ◇ (z ◇ z))]

theorem Equation4512_41787_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41787 : Equation41787 G) : Equation327 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h41787 X1 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41787 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41787 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (X0 ◇ X0))]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41787 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ (X0 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h41787 X1 X0 X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41787 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l4 X0 X1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l4 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK2 X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l10 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ ((sK2 ◇ (X0 ◇ X0)) ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK2 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l2 sK1 sK2 X0]
  have l11 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = ((sK1 ◇ sK2) ◇ (sK2 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l10 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 (X0 ◇ X0) X1]
  have l12 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = ((sK1 ◇ sK2) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l11 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← l8 sK1 sK2 ((X0 ◇ X0) ◇ X1)]
  have l13 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l12 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l14 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l13 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l5 (sK1 ◇ sK2) X1 X0]
  have l15 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h41787 X1 (sK1 ◇ sK2) X1]
    conv => enter [1, 2]; rw [l14 sK1 sK2 ((sK1 ◇ sK2) ◇ (X1 ◇ X1)) X0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK2]
  have l17 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (X0 ◇ X0)) ◇ X1)) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l1 sK0 sK1 X0]
  have l18 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ X1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l17 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (X0 ◇ X0) X1]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 (sK0 ◇ sK1) sK1 sK2 sK2]
  have l20 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ X1) = ((sK0 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l9 sK0 sK1 ((X0 ◇ X0) ◇ X1)]
  have l21 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ X1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l22 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l21 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK1) X1 X0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X0]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 sK0]
    conv => enter [1]; rw [l22 sK0 sK1 (sK1 ◇ sK0) X0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l25 x y z]

@[equational_result]
theorem Equation327_implies_Equation41788 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41788 G := by
  intro x y z w
  conv => enter [1]; rw [h327 x y (y ◇ (z ◇ w))]

theorem Equation4512_41788_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41788 : Equation41788 G) : Equation327 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41788 X1 X0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41788 X0 X0 X1 X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41788 X0 X1 X2 X3]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l3 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ X3)) X4]
  have l4 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X3) X4]
  have l5 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X4)) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41788 X0 X1 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l4 X0 X1 X4 X0 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK1) sK1 X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l10 x y z]

@[equational_result]
theorem Equation327_implies_Equation41789 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41789 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (z ◇ (x ◇ x))]

theorem Equation4512_41789_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41789 : Equation41789 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41789 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41789 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41789 (sK0 ◇ sK1) sK2 X0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 sK1]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41789 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l10 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation327_implies_Equation41791 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41791 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (z ◇ (x ◇ z))]

end Semigroup5
