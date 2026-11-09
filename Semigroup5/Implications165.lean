import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_42053_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42053 : Equation42053 G) : Equation41 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h42053 X0 X2 (X1 ◇ (X0 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h42053 X0 X1 X2]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h42053 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h42053 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK1 ◇ X0)]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X2) (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X2 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ X0 X2 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X2
    conv => enter [1]; rw [l4 X0 X2 X0]
    conv => enter [1]; rw [← l1 X0 X2 X0 X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l5 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l5 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ sK2)]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l8 sK1 sK2 X0]
  have l10 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK1 X0]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1, 2]; rw [l5 sK2 sK1]
  have l12 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (sK1 ◇ (sK2 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h42053 sK2 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l5 sK2 sK1]
  have l13 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l12 sK2 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
  have l14 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l15 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l13 sK2 X0 sK1]
    conv => enter [1]; rw [← l6 (sK1 ◇ sK2) X0 sK2]
  have l16 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l15 sK2 X0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK2 X0]
  have l17 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ sK2) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1)))) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h42053 X0 sK2 X1]
    conv => enter [1, 2, 2]; rw [l16 sK2 (X0 ◇ X1) sK1]
  have l18 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ sK2) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h42053 X0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l17 X0 sK2 X0 sK1]
  have l19 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h42053 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [l18 sK1 sK1 sK2]
  have l20 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l19 sK1 X0 sK2]
    conv => enter [1]; rw [← l6 (sK1 ◇ sK2) sK1 X0]
  have l21 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 X0]
    conv => enter [1]; rw [← l20 sK1 X0 sK2]
  have l22 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l21 sK1 sK2 X0]
  have l23 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l22 sK1 sK2 X0]
    conv => enter [1]; rw [← l6 X0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l24 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l23 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l14 sK1 sK2]
  have l25 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l24 sK1 sK2 X0]
  have l26 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l24 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l25 sK1 sK2 X0]
  have l27 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42053 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l26 sK1 sK2 (X0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2))))]
  intro x y z
  conv => enter [1]; rw [l27 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42054 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42054 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42054_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42054 : Equation42054 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42054 sK0 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h42054 X1 X0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h42054 X0 X1 X1 X1]
  have l2 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h42054 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK1 ◇ X0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ X0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
    conv => enter [1]; rw [← l1 ((sK0 ◇ sK0) ◇ X0) sK0 sK0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ X0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK1 X0]
    conv => enter [1]; rw [← l1 (sK1 ◇ X0) (sK1 ◇ sK2) sK1]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 sK0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK1 ◇ sK2)]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK2) X0 sK1]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42054 X0 X1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l8 sK1 sK2 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42054 X0 X1 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42055 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42055 G := by
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
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42055_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42055 : Equation42055 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ sK0) = (X1 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42055 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK2 X0 sK1 X1 : G, ((sK2 ◇ X0) ◇ sK1) = (X1 ◇ ((sK2 ◇ X0) ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 sK1 X1
    conv => enter [1]; rw [h42055 (sK2 ◇ X0) sK1 X1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42055 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h42055 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK2 ◇ sK1)]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42055 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42055 X0 X1 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK2 X0 sK1 X1 : G, ((sK2 ◇ X0) ◇ sK1) = (X1 ◇ (sK2 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))))) := by
    intro sK2 X0 sK1 X1
    conv => enter [1]; rw [l2 sK2 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ sK0) = (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42055 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [← l6 (sK1 ◇ sK2) (sK2 ◇ sK1) sK1]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l6 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ X0) ◇ sK1) = (sK2 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l8 sK2 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 X0 (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) sK2]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l6 X0 (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2]
    conv => enter [1]; rw [← l6 sK2 sK1 (sK1 ◇ sK2)]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1, 2]; rw [← l6 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l18 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ X0) ◇ sK1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l13 sK2 X0 sK1]
    conv => enter [1]; rw [← l6 X0 (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) sK2]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l6 X0 (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l21 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ X0) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l18 sK2 X0 sK1]
    conv => enter [1]; rw [← l6 sK1 ((sK1 ◇ sK2) ◇ X0) X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ X0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ sK0) ◇ X0) X0]
    conv => enter [1]; rw [← l19 sK0 X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l20 sK0]
  have l24 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK2 ◇ X0) ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1]; rw [← l21 sK2 X0 sK1]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 sK0]
  have l26 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l24 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 sK1]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← l6 X0 sK0 sK0]
  have l28 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l26 sK1 sK2 X0]
    conv => enter [1]; rw [← l6 X0 sK1 sK2]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l30 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
  have l31 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l30 sK1 sK2 X0]
    conv => enter [1]; rw [← l6 sK1 X0 sK2]
  have l32 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((X0 ◇ sK1) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1, 1]; rw [l28 sK1 sK2 X0]
  have l33 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l28 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l34 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [← l28 sK1 sK2 sK2]
  have l35 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X1 ◇ sK1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l33 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l6 X1 sK1 X0]
  have l36 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l32 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 sK1 X1]
  have l37 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X1 ◇ sK1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l6 X0 X1 (sK1 ◇ X0)]
    conv => enter [1]; rw [l35 sK1 X0 X0 X1]
  have l38 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK1 ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l36 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l6 sK1 X1 X0]
  have l39 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l38 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l31 sK1 sK2 X1]
  have l40 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l39 sK1 sK2 X0 X1]
  have l41 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l42 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l43 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l29 sK0 sK2]
  have l44 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l43 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) sK2 sK1]
  have l45 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X1 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l42 sK0 X0 X1]
    conv => enter [1]; rw [← l6 X1 sK0 X0]
  have l46 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l41 sK0 X0 X1]
    conv => enter [1]; rw [← l6 sK0 X1 X0]
  have l47 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l40 (sK1 ◇ sK2) sK2 sK0 sK0]
    conv => enter [1]; rw [← l44 sK1 sK2 sK0]
  have l48 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l45 sK0 X0 X1]
  have l49 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l46 sK0 X0 X1]
  have l50 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l47 sK1 sK2 sK0]
    conv => enter [1]; rw [l37 (sK1 ◇ sK2) sK0 sK1]
  have l51 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l49 sK0 X0 X1]
  have l52 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [l50 sK1 sK2 sK0]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [← l52 sK1 sK2 sK0]
  have l54 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l51 sK0 (sK0 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l54 sK1 sK2 sK0]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
  have l57 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l56 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [l37 (sK0 ◇ sK0) (sK1 ◇ sK2) sK1]
  have l59 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l58 sK0 sK1 sK2]
    conv => enter [1]; rw [← l28 sK1 sK2 (sK1 ◇ sK2)]
  have l60 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
    conv => enter [1]; rw [l48 (sK1 ◇ sK2) (sK1 ◇ sK2) sK0]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1 sK0]
    conv => enter [1]; rw [l37 (sK1 ◇ sK0) sK0 sK1]
  have l62 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l52 sK1 sK2 sK0]
    conv => enter [1]; rw [← l61 sK0 sK1]
  have l63 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l62 sK1 sK2 sK0]
    conv => enter [1]; rw [← l23 sK0]
  intro x y z
  conv => enter [1]; rw [← l63 y z x]

@[equational_result]
theorem Equation41_implies_Equation42057 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42057 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42057_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42057 : Equation42057 G) : Equation41 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h42057 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK2 ◇ X0)]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((X0 ◇ (X0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h42057 sK2 X0 (sK1 ◇ sK2)]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ ((X0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK1 ◇ sK2)) (sK2 ◇ X0)]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK2) (sK2 ◇ X0)]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l0 sK1 sK2 X0]
  have l5 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42057 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1 sK2 X1]
  have l6 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l5 X0 X1 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK2 X1]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 X0]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l4 sK1 sK2 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l8 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42058 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42058 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42058_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42058 : Equation42058 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42058 X2 X0 X3 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h42058 X0 X1 X0 X2]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h42058 X1 X0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h42058 X0 X0 X1 X1]
  have l2 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h42058 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK2 ◇ X0)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42058 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X1 ◇ X4)))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42058 X0 X1 X0 X0]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l0 (sK1 ◇ sK2) sK2 sK1 sK1]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK2 X0]
  have l7 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l4 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK1 sK2 X0]
  have l8 : ∀ X1 sK2 X2 sK1 X0 : G, (X1 ◇ sK2) = (X2 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)))) := by
    intro X1 sK2 X2 sK1 X0
    conv => enter [1]; rw [h42058 X1 sK2 X2 X0]
    conv => enter [1, 2, 2]; rw [l7 sK2 (sK2 ◇ X0) sK1]
  have l9 : ∀ X1 sK2 sK1 : G, (X1 ◇ sK2) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X1 sK2 sK1
    conv => enter [1]; rw [l8 X1 sK2 X1 sK1 X1]
    conv => enter [1]; rw [← l0 X1 (sK1 ◇ sK2) X1 (sK2 ◇ X1)]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l9 (sK1 ◇ sK2) sK2 sK1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← l1 X2 X1 X0]
  have l12 : ∀ X3 X1 X4 X0 X2 : G, (X3 ◇ X1) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X1 X4 X0 X2
    conv => enter [1]; rw [h42058 X3 X1 X4 X2]
    conv => enter [1, 2, 2]; rw [l11 X1 (X1 ◇ X2) X0]
  have l13 : ∀ X3 X0 X1 : G, (X3 ◇ X0) = (X3 ◇ X1) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l12 X3 X0 X3 X1 X3]
    conv => enter [1]; rw [← l0 X3 X1 X3 (X0 ◇ X3)]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l13 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 sK0 X0]
  have l15 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l14 (sK1 ◇ sK2) (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l15 y z x]

@[equational_result]
theorem Equation41_implies_Equation42059 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42059 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42059_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42059 : Equation42059 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h42059 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42059 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42059 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0)))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42059 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X3 X0]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h42059 (sK0 ◇ sK0) X0 sK0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← l1 X0 X1 X2 X0]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← l1 X1 X2 X3 X0]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l9 X1 X2 X1]
    conv => enter [1]; rw [← l10 X0 X1 X2 X1]
  have l12 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h42059 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l8 sK0 (X0 ◇ X1)]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42059 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l8 sK0 X0]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l13 X0 X1 sK0]
    conv => enter [1]; rw [← l11 X0 (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) sK0]
  have l15 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [h42059 X1 sK0 X1]
    conv => enter [1]; rw [← l12 X1 sK0 X1]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l14 X0 X1 sK0]
    conv => enter [1]; rw [← l9 X1 (sK0 ◇ sK0) X0]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h42059 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l16 X2 X0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l16 X0 (sK0 ◇ sK0) sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l17 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l11 X1 (X0 ◇ (sK0 ◇ sK0)) X0]
  have l21 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1]; rw [← l11 X1 (X0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l21 X0 X1 sK0]
    conv => enter [1]; rw [← l11 X0 (sK0 ◇ sK0) X1]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l22 X0 X1 sK0]
    conv => enter [1]; rw [← l19 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l23 y z x]

@[equational_result]
theorem Equation41_implies_Equation42062 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42062 G := by
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
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42062_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42062 : Equation42062 G) : Equation41 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ X1)) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [h42062 X4 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42062 X2 X0 X1 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h42062 X0 X1 X2 X2]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42062 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X3 X4]
  have l4 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l3 X0 X1 X0 X3 X0]
    conv => enter [1]; rw [← l0 X3 X0 X1 X0 (X3 ◇ X0)]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← l1 X2 X1 X0]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 sK0 X1]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 X1]
    conv => enter [1]; rw [← l4 sK0 X1 X1]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42063 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42063 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK1)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_42063_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42063 : Equation42063 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ X1) = (X2 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42063 (sK0 ◇ X0) X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X3 X0 X1 X4 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X0 X1 X4 X2
    conv => enter [1]; rw [h42063 X3 (X0 ◇ X1) X4 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42063 sK0 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42063 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X4 ◇ X0)))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42063 X0 X1 X0 X0]
  have l6 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ X1) = (X2 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l1 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 X0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) (X0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l5 X0 (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l5 X0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X1 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← l5 X1 sK0 X0]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X1]
    conv => enter [1]; rw [← l11 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 X1]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1]; rw [← l13 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l14 y z x]

@[equational_result]
theorem Equation41_implies_Equation42065 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42065 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 (sK0 ◇ sK3)]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0 sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_42065_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42065 : Equation42065 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = ((sK0 ◇ X0) ◇ (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h42065 X1 X2 (sK0 ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = ((X3 ◇ X2) ◇ (X0 ◇ X1)) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42065 X2 X0 (X3 ◇ X2) X1]
    conv => enter [1, 2]; rw [← h42065 X0 X1 X2 X3]
  have l3 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l2 X2 X0 X3 X1]
    conv => enter [1]; rw [← h4512 X3 X2 (X0 ◇ X1)]
  have l4 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (sK0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l1 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ X1) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l4 X1 X2 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1 X1 (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))]
  have l6 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l5 sK0 sK0 X0]
    conv => enter [1]; rw [l5 X0 sK0 X1]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42066 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42066 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 sK1 sK2 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [h41 sK0 sK3 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK1]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_42066_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42066 : Equation42066 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42066 sK0 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h42066 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42066 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X4 ◇ X4)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42066 X0 X1 X0 X0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 X0]
    conv => enter [1]; rw [← l3 (sK1 ◇ sK2) (X0 ◇ X0) sK1]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) (X0 ◇ X0) sK0]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ sK2) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l3 X0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK1 sK2 X0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l6 sK1 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation42067 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42067 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK3 (sK1 ◇ sK0)]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK2 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

theorem Equation4512_42067_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42067 : Equation42067 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ sK0) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [h42067 sK0 sK0 X2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42067 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X4 ◇ X5)))]
  have l3 : ∀ sK0 X0 X1 X2 X3 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h42067 X0 X1 sK0 X2 X3]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l4 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42067 sK0 X0 (sK0 ◇ sK0) X1 X2]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X1 ◇ X2))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h42067 (sK0 ◇ sK0) X0 sK0 sK0 sK0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42067 X0 X1 (sK0 ◇ sK0) X0 X0]
    conv => enter [1]; rw [← l3 sK0 X0 X1 X0 X0]
  have l7 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X3 ◇ X0) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l2 X0 X1 X0 X3 X0 X0]
    conv => enter [1]; rw [← h42067 X3 X0 X0 X1 (X0 ◇ X0)]
  have l8 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l1 sK0 X2 X0 X1]
    conv => enter [1, 2]; rw [← l5 sK0 (X0 ◇ X1)]
  have l9 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X0 ◇ X1)) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l8 sK0 X2 X0 X1]
    conv => enter [1, 2]; rw [← l6 X0 X1 sK0]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42068 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42068 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41 sK0 sK2 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x z]

theorem Equation4512_42068_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42068 : Equation42068 G) : Equation41 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h42068 sK0 (sK0 ◇ X1) X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l1 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42068 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 X1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42068 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42070 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42070 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation42070_implies_Equation41 (G : Type*) [Magma G] (h42070 : Equation42070 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42070 X0 X1 X0]
    conv => enter [1]; rw [← h42070 X0 X2 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42070 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42071 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42071 G := by
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
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42071_implies_Equation41 (G : Type*) [Magma G] (h42071 : Equation42071 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42071 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42071 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42071 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42072 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42072 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42072_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42072 : Equation42072 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h42072 (sK0 ◇ X0) (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42072 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h42072 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h42072 X0 X1 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42072 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ X0)))]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42072 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (X1 ◇ X0)))]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X3 (X1 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 X0 sK0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l9 sK0 X0 X0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ sK0)]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42072 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [l12 X0 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42072 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l16 y z x]

@[equational_result]
theorem Equation41_implies_Equation42075 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42075 G := by
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
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42075_implies_Equation41 (G : Type*) [Magma G] (h42075 : Equation42075 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42075 X2 X0 X3 (X3 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h42075 X0 X1 X3 X2]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h42075 X0 sK0 X1 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42075 X0 X1 sK0 X0]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ (X1 ◇ X0))) sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42076 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42076 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation42076_implies_Equation41 (G : Type*) [Magma G] (h42076 : Equation42076 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42076 X0 X1 X0]
    conv => enter [1]; rw [← h42076 X0 X2 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42076 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42078 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42078 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK0 (sK2 ◇ (sK2 ◇ sK2))]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h41 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z x]

@[equational_result]
theorem Equation42078_implies_Equation41 (G : Type*) [Magma G] (h42078 : Equation42078 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42078 X0 X1 X0]
    conv => enter [1]; rw [← h42078 X0 X2 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42078 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42079 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42079 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42079_implies_Equation41 (G : Type*) [Magma G] (h42079 : Equation42079 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42079 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42079 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42079 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42080 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42080 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK1]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK1)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [← l0 sK1 sK3 sK0]
    conv => enter [1, 2]; rw [l3 sK1 sK3 sK3 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation42080_implies_Equation41 (G : Type*) [Magma G] (h42080 : Equation42080 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42080 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42080 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42080 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42082 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42082 G := by
  have l0 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK0 ◇ sK3) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK3]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK3)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK3 sK1 sK3]
    conv => enter [1, 2]; rw [l3 sK1 sK3 sK3 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation42082_implies_Equation41 (G : Type*) [Magma G] (h42082 : Equation42082 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42082 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42082 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42082 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42083 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42083 G := by
  have l0 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK1 (sK3 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h41 sK0 sK3 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK1]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation42083_implies_Equation41 (G : Type*) [Magma G] (h42083 : Equation42083 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42083 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42083 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42083 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42084 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42084 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ sK0) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 sK0]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ sK0)]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK2 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK4 sK1 sK0]
  have l4 : ∀ sK4 sK1 sK0 sK2 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK4 ◇ (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK2 sK4]
    conv => enter [1, 2]; rw [l3 sK2 sK4 sK4 sK1 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l4 sK4 sK1 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

@[equational_result]
theorem Equation42084_implies_Equation41 (G : Type*) [Magma G] (h42084 : Equation42084 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42084 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42084 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42084 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42085 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42085 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK0 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l2 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h41 sK1 sK3 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l2 x z w]

theorem Equation4512_42085_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42085 : Equation42085 G) : Equation41 G := by
  have l0 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [← h42085 sK0 (sK0 ◇ X2) X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l1 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [h42085 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 X2]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42085 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42087 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42087 G := by
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
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42087_implies_Equation41 (G : Type*) [Magma G] (h42087 : Equation42087 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42087 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42087 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42087 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42088 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42088 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42088_implies_Equation41 (G : Type*) [Magma G] (h42088 : Equation42088 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42088 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42088 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42088 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42089 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42089 G := by
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
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK2 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42089_implies_Equation41 (G : Type*) [Magma G] (h42089 : Equation42089 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42089 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42089 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42089 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42090 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42090 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42090_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42090 : Equation42090 G) : Equation41 G := by
  have l0 : ∀ X3 X2 X4 X0 X1 : G, (X3 ◇ X2) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X2 X4 X0 X1
    conv => enter [1]; rw [h42090 X3 X2 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X0 X1 X3 X4 X2 : G, ((X0 ◇ X1) ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X3 X4 X2
    conv => enter [1]; rw [h42090 (X0 ◇ X1) X3 X4 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42090 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X4 ◇ (X1 ◇ X0)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42090 X0 X1 X0 X0]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X3 X4 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X1 X3 X4 X0 X2 : G, (X1 ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X1 X3 X4 X0 X2
    conv => enter [1]; rw [l3 X1 X3 X0]
    conv => enter [1]; rw [← l4 X4 X0 X1 X2 X3]
  have l6 : ∀ X1 X3 X0 X2 : G, (X1 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X1 X3 X0 X2
    conv => enter [1]; rw [l5 X1 X3 X1 X0 X2]
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) X1]
  have l7 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X1 ◇ X0) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l6 X1 X3 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0 X0 X1 X3]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42090 X0 X1 sK0 X0]
    conv => enter [1]; rw [l7 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X0))) sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1]
    conv => enter [1]; rw [l8 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42092 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42092 G := by
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
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42092_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42092 : Equation42092 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X4 X1 X5 : G, (X2 ◇ X3) = ((X0 ◇ (X4 ◇ (X1 ◇ X3))) ◇ (X2 ◇ (X5 ◇ (X0 ◇ X1)))) := by
    intro X2 X3 X0 X4 X1 X5
    conv => enter [1]; rw [h42092 X2 X3 (X0 ◇ (X4 ◇ (X1 ◇ X3))) X5]
    conv => enter [1, 2, 2, 2]; rw [← h42092 X0 X1 X3 X4]
  have l1 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X0 X1 X2 X4
    conv => enter [1]; rw [h42092 X3 (X0 ◇ X1) X2 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X4 X2 X3 X0 X1 : G, (X4 ◇ X2) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X2 X3 X0 X1
    conv => enter [1]; rw [h42092 X4 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l1 X3 X0 X1 X3 X3]
    conv => enter [1]; rw [← l2 X3 X1 X3 X3 X0]
  have l4 : ∀ X2 X3 X0 X4 X1 X5 : G, (X2 ◇ X3) = (X0 ◇ ((X4 ◇ (X1 ◇ X3)) ◇ (X2 ◇ (X5 ◇ (X0 ◇ X1))))) := by
    intro X2 X3 X0 X4 X1 X5
    conv => enter [1]; rw [l0 X2 X3 X0 X4 X1 X5]
    conv => enter [1]; rw [← h4512 X0 (X4 ◇ (X1 ◇ X3)) (X2 ◇ (X5 ◇ (X0 ◇ X1)))]
  have l5 : ∀ X2 X3 X0 X5 X1 : G, (X2 ◇ X3) = (X0 ◇ (X2 ◇ (X5 ◇ (X0 ◇ X1)))) := by
    intro X2 X3 X0 X5 X1
    conv => enter [1]; rw [l4 X2 X3 X0 X2 X1 X5]
    conv => enter [1]; rw [l3 X0 (X2 ◇ (X1 ◇ X3)) (X2 ◇ (X5 ◇ (X0 ◇ X1)))]
  have l6 : ∀ X2 X3 X0 X5 X1 : G, (X2 ◇ X3) = (X0 ◇ (X5 ◇ (X0 ◇ X1))) := by
    intro X2 X3 X0 X5 X1
    conv => enter [1]; rw [l5 X2 X3 X0 X5 X1]
    conv => enter [1]; rw [l3 X0 X2 (X5 ◇ (X0 ◇ X1))]
  have l7 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l6 X2 X3 X0 X2 X1]
    conv => enter [1]; rw [l3 X0 X2 (X0 ◇ X1)]
  have l8 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ X1) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l7 X2 X3 X0 X1]
    conv => enter [1]; rw [l3 X0 X0 X1]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42093 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42093 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42093_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42093 : Equation42093 G) : Equation41 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42093 X2 X0 X3 (X2 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h42093 X0 X1 (X2 ◇ (X1 ◇ X2)) X2]
  have l1 : ∀ X2 X1 X3 X0 : G, (X2 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [h42093 X2 X1 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h42093 (X0 ◇ X1) X0 X2 X1]
  have l2 : ∀ X2 X1 X3 X0 : G, (X2 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l1 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X0]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ sK2) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h42093 X0 sK1 X0 sK2]
    conv => enter [1]; rw [← l0 X0 sK2 X0 (sK1 ◇ sK2)]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X0 X2]
    conv => enter [1]; rw [← l0 X2 X1 X0 X2]
  have l5 : ∀ X1 X0 X2 sK2 sK1 : G, (X1 ◇ X0) = (X2 ◇ (X1 ◇ (sK2 ◇ (X0 ◇ sK1)))) := by
    intro X1 X0 X2 sK2 sK1
    conv => enter [1]; rw [h42093 X1 X0 X2 sK2]
    conv => enter [1, 2, 2, 2]; rw [l3 X0 sK2 sK1]
  have l6 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ sK2) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l5 X1 X0 X1 sK2 X1]
    conv => enter [1]; rw [← l0 X1 sK2 X1 (X0 ◇ X1)]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ X1)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 X1]
  have l8 : ∀ X0 X1 X2 sK2 : G, (X0 ◇ X1) = (X2 ◇ sK2) := by
    intro X0 X1 X2 sK2
    conv => enter [1]; rw [l7 X0 X1 X2 X0]
    conv => enter [1]; rw [l6 X2 (X0 ◇ X1) sK2]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l8 X0 X1 X0 sK2]
    conv => enter [1]; rw [l4 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l9 x x y z]

@[equational_result]
theorem Equation41_implies_Equation42094 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42094 G := by
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
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK2 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation4512_42094_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42094 : Equation42094 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X1 ◇ X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42094 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X4 ◇ (X1 ◇ X5)))]
  have l1 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [l0 X0 X1 X0 X3 X4 X0]
    conv => enter [1]; rw [← h42094 X3 X4 X0 X0 (X1 ◇ X0)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42095 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42095 G := by
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
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42095_implies_Equation41 (G : Type*) [Magma G] (h42095 : Equation42095 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42095 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42095 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42095 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42097 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42097 G := by
  have l0 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ sK3) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [h41 sK3 sK1 (sK0 ◇ (sK3 ◇ sK3))]
  have l1 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [h41 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l1 z x w]

@[equational_result]
theorem Equation42097_implies_Equation41 (G : Type*) [Magma G] (h42097 : Equation42097 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42097 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42097 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42097 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42098 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42098 G := by
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
  have l3 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42098_implies_Equation41 (G : Type*) [Magma G] (h42098 : Equation42098 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42098 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42098 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42098 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42099 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42099 G := by
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
  have l3 : ∀ sK2 sK3 sK1 sK4 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ (sK4 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK4 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK2 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK4 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK4 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l3 sK2 sK3 sK1 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

@[equational_result]
theorem Equation42099_implies_Equation41 (G : Type*) [Magma G] (h42099 : Equation42099 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42099 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42099 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42099 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42100 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42100 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation42100_implies_Equation41 (G : Type*) [Magma G] (h42100 : Equation42100 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42100 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42100 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42100 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42102 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42102 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ (sK0 ◇ sK3))]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation42102_implies_Equation41 (G : Type*) [Magma G] (h42102 : Equation42102 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42102 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42102 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42102 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42103 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42103 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h41 sK0 sK3 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK1 sK0 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

@[equational_result]
theorem Equation42103_implies_Equation41 (G : Type*) [Magma G] (h42103 : Equation42103 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42103 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42103 X0 X2 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42103 X0 X1 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42104 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42104 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK1 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

@[equational_result]
theorem Equation42104_implies_Equation41 (G : Type*) [Magma G] (h42104 : Equation42104 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42104 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42104 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42104 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42105 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42105 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK1 ◇ (sK0 ◇ sK2))]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

@[equational_result]
theorem Equation42105_implies_Equation41 (G : Type*) [Magma G] (h42105 : Equation42105 G) : Equation41 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h42105 X0 X2 X0 X0 X0]
    conv => enter [1]; rw [← h42105 X0 X1 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42105 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42107 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42107 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 sK4 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK1 ◇ (sK0 ◇ sK4))]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

@[equational_result]
theorem Equation42107_implies_Equation41 (G : Type*) [Magma G] (h42107 : Equation42107 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42107 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42107 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42107 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42108 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42108 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK1 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

@[equational_result]
theorem Equation42108_implies_Equation41 (G : Type*) [Magma G] (h42108 : Equation42108 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42108 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42108 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42108 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42109 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42109 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK0 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK0 sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41 sK0 sK2 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l2 sK0 sK2 sK1]
  have l4 : ∀ sK0 sK4 sK2 sK1 : G, (sK0 ◇ sK0) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK2 sK1
    conv => enter [1]; rw [h41 sK0 sK4 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK2 sK0 sK1 sK0]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK0 sK4 sK2 sK1]
  intro x y z w u
  conv => enter [1]; rw [l5 x y z w u]

@[equational_result]
theorem Equation42109_implies_Equation41 (G : Type*) [Magma G] (h42109 : Equation42109 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42109 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42109 X0 X2 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42109 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42109 X0 X1 sK1 X0 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation41_implies_Equation42110 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42110 G := by
  have l0 : ∀ X1 X2 sK3 sK4 : G, (X1 ◇ X2) = (sK3 ◇ sK4) := by
    intro X1 X2 sK3 sK4
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK3 sK4]
  have l1 : ∀ sK3 sK4 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK4]
    conv => enter [1]; rw [h41 sK3 sK3 (sK2 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 sK5 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l1 sK3 sK4 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l2 x y z w u v]

@[equational_result]
theorem Equation42110_implies_Equation41 (G : Type*) [Magma G] (h42110 : Equation42110 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42110 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h42110 X0 X2 X0 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42110 X0 X1 sK0 X0 X0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42111 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42111 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x z (y ◇ (x ◇ (x ◇ x)))]

theorem Equation4512_42111_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42111 : Equation42111 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42111 (X0 ◇ (X0 ◇ X0)) X1 X2]
    conv => enter [1, 2, 2]; rw [← h42111 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42111 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42111 X0 X1 X0]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h42111 X0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0 X0]
    conv => enter [1]; rw [← l3 X0 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0]
    conv => enter [1]; rw [← l7 X0 X1]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 X0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42111 X0 X1 sK0]
    conv => enter [1]; rw [l8 sK0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l11 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42111 X0 X1 sK1]
    conv => enter [1]; rw [l9 sK1 (X1 ◇ (X0 ◇ (X0 ◇ X0))) sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

@[equational_result]
theorem Equation41_implies_Equation42113 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42113 G := by
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
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42113_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42113 : Equation42113 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h42113 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h42113 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h42113 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h42113 sK0 sK0 sK0]
  have l4 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42113 sK0 X1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← h42113 sK0 X0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ X0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) (X1 ◇ (sK0 ◇ (sK0 ◇ X0)))]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l0 sK0 sK0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1
    conv => enter [1]; rw [l7 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l9 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X1)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42113 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← l13 sK0 (X0 ◇ (X0 ◇ X1))]
  have l16 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h42113 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK0 (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0))))]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h42113 X0 sK0 X0]
    conv => enter [1]; rw [← l15 X0 sK0 X0]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42113 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 sK0]
    conv => enter [1]; rw [← l18 sK0 X0 X1]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 sK0]
    conv => enter [1]; rw [← l13 sK0 (X0 ◇ X1)]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42113 sK0 X0 sK0]
    conv => enter [1]; rw [← l20 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1, 2]; rw [← l17 sK0 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l17 X0 sK0]
  have l24 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l25 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l22 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l26 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l22 sK0 sK2]
  have l27 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l17 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [l26 sK1 sK2 sK0]
  have l28 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l25 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l17 X1 sK0]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l24 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l13 sK0 X1]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1]; rw [l28 sK0 X0 X1]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l29 sK0 X0 X1]
  have l33 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK0]
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
  have l34 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1]; rw [l32 sK0 X0 X1]
  have l35 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42113 sK0 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l23 sK0 X0]
  have l36 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l35 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l34 X1 (X0 ◇ sK0) sK0]
  have l37 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l36 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l31 X1 X0 sK0]
  have l38 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42113 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l31 X0 X0 sK0]
  have l39 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l38 X0 X1 X0]
    conv => enter [1]; rw [← l20 X1 (X0 ◇ X0) X0]
  have l40 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [← l34 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) sK0]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l40 X0 sK0]
  have l42 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42113 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l41 sK0 X0]
  have l43 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l42 X0 X1 sK0]
    conv => enter [1]; rw [← l13 sK0 (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l44 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l43 X0 X1 sK0]
    conv => enter [1]; rw [← l20 X1 (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) sK0]
  have l45 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l44 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l37 sK0 (sK0 ◇ sK0) X0]
  have l46 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l45 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l34 sK0 sK0 sK0]
  have l47 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l46 X0 X1 sK0]
    conv => enter [1]; rw [← l17 X1 sK0]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l46 X0 sK0 sK0]
  have l49 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l47 X0 X1 sK0]
    conv => enter [1]; rw [← l48 sK0 X1]
  have l50 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [l49 sK1 (sK0 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l50 y z x]

@[equational_result]
theorem Equation41_implies_Equation42114 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42114 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42114_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42114 : Equation42114 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ X1) = (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h42114 sK0 X1 X2 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h42114 X1 X2 X3 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h42114 X0 X1 X1 X1]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42114 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ (X0 ◇ X4)))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42114 X0 X1 X0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 ((sK0 ◇ sK0) ◇ X0) X1 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 X1 sK0 X0]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ X0 X2 X3 sK0 X1 : G, (X0 ◇ X2) = (X3 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X2 X3 sK0 X1
    conv => enter [1]; rw [h42114 X0 X2 X3 X1]
    conv => enter [1, 2]; rw [l6 X2 (X0 ◇ (X0 ◇ X1)) sK0]
  have l8 : ∀ X0 sK0 X2 : G, (X0 ◇ sK0) = (X0 ◇ X2) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h42114 X0 sK0 X0 X0]
    conv => enter [1]; rw [← l7 X0 X2 X0 sK0 X0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l6 sK0 sK0 X0]
    conv => enter [1]; rw [l8 X0 sK0 X2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation41_implies_Equation42115 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42115 G := by
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
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42115_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42115 : Equation42115 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK2 X0 sK1 X1 : G, ((sK2 ◇ X0) ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK2 ◇ X0) ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 sK1 X1
    conv => enter [1]; rw [h42115 (sK2 ◇ X0) sK1 X1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h42115 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 sK1]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42115 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42115 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42115 X0 X1 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l7 : ∀ sK2 X0 sK1 X1 : G, ((sK2 ◇ X0) ◇ sK1) = (X1 ◇ (sK1 ◇ (sK2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))))) := by
    intro sK2 X0 sK1 X1
    conv => enter [1]; rw [l1 sK2 X0 sK1 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 X0 ((sK1 ◇ sK2) ◇ X0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 (sK0 ◇ sK0) sK0 sK0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [← l5 sK2 ((sK1 ◇ sK2) ◇ sK1) sK1]
  have l10 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ X0) ◇ sK1) = (sK1 ◇ (sK2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l7 sK2 X0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 (sK2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) sK2]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) sK0 sK0]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [← l5 (sK1 ◇ sK2) sK1 sK2]
  have l13 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ X0) ◇ sK1) = (sK2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l10 sK2 X0 sK1]
    conv => enter [1]; rw [← l5 sK2 (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) sK1]
  have l14 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ X0) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l13 sK2 X0 sK1]
    conv => enter [1]; rw [← l5 X0 ((sK1 ◇ sK2) ◇ X0) sK2]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK2 ◇ X0) ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 (sK1 ◇ sK2) X0 X0]
    conv => enter [1]; rw [← l14 sK2 X0 sK1]
  have l16 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 sK1]
  have l17 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK2 X0]
    conv => enter [1]; rw [← l5 X0 sK1 sK2]
  have l18 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [h42115 X0 (sK1 ◇ sK2) X1]
    conv => enter [1, 2, 2, 2]; rw [l17 sK1 sK2 X0]
  have l19 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l17 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l20 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (X1 ◇ sK1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l19 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l5 X1 sK1 X0]
  have l21 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l18 X0 sK1 sK2 X0]
    conv => enter [1]; rw [← l5 (sK1 ◇ sK2) (X0 ◇ (X0 ◇ sK1)) X0]
  have l22 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X1 ◇ sK1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l5 X0 X1 (sK1 ◇ X0)]
    conv => enter [1]; rw [l20 sK1 X0 X0 X1]
  have l23 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l21 X0 sK1 sK2]
    conv => enter [1]; rw [← l5 X0 (X0 ◇ sK1) (sK1 ◇ sK2)]
  have l24 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 X0]
    conv => enter [1]; rw [← l23 X0 sK1 sK2]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l22 (sK0 ◇ sK0) sK0 sK1]
  have l26 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [← l22 X0 (sK1 ◇ sK2) sK1]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2 sK0]
    conv => enter [1]; rw [← l27 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l28 y z x]

@[equational_result]
theorem Equation41_implies_Equation42117 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42117 G := by
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
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42117_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42117 : Equation42117 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42117 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42117 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h42117 X1 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h42117 X0 X1 X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42117 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ X1)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l5 X0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l7 X1 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l7 X0 sK0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42117 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK0 X1]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l7 X0 sK0]
  have l18 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l17 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l14 sK0 X1 X0]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l18 X0 X1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l19 y z x]

@[equational_result]
theorem Equation41_implies_Equation42118 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42118 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42118_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42118 : Equation42118 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42118 sK0 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h42118 sK1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X1 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h42118 X0 X1 X0 X2]
    conv => enter [1]; rw [← h42118 X1 X0 X2 (X1 ◇ X2)]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (((sK1 ◇ sK2) ◇ X0) ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 X0]
    conv => enter [1]; rw [l2 sK1 sK2 ((sK1 ◇ sK2) ◇ X0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ X0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
    conv => enter [1]; rw [l2 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) X0 sK2]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 sK0]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [l2 (sK1 ◇ sK2) X0 sK2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) X0 sK0]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42118 X0 X1 sK2 X0]
    conv => enter [1]; rw [← l7 sK1 sK2 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42118 X0 X1 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

@[equational_result]
theorem Equation41_implies_Equation42119 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42119 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42119_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42119 : Equation42119 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42119 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42119 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h42119 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42119 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1, 2]; rw [← l7 sK0]
  have l12 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42119 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l9 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l7 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h42119 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← l10 sK0 (X0 ◇ (X1 ◇ X0))]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h42119 X0 sK0 X0]
    conv => enter [1]; rw [← l17 X0 sK0 X0]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42119 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
    conv => enter [1, 2]; rw [← h42119 X0 X1 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42119 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l9 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 sK0]
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ X1)]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1, 2]; rw [← l16 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42119 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l26 sK0 X0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l27 X0 X1 sK0]
    conv => enter [1]; rw [← l22 X1 (sK0 ◇ sK0) sK0]
  have l29 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l28 X0 X1 sK0]
    conv => enter [1]; rw [← l18 X1 sK0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l28 X0 sK0 sK0]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l29 X0 X1 sK0]
    conv => enter [1]; rw [← l30 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l31 y z x]

@[equational_result]
theorem Equation41_implies_Equation42122 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42122 G := by
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
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42122_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42122 : Equation42122 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h42122 X1 X2 X0 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [← h42122 X0 X1 X2 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← l0 X0 X2 X0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) sK1 sK0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ X0) sK0]
  have l6 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l5 (sK0 ◇ sK0) sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l7 y z x]

@[equational_result]
theorem Equation41_implies_Equation42123 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42123 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_42123_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42123 : Equation42123 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ X3) = (X4 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h42123 X2 X3 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ X1) = (X2 ◇ (X1 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h42123 (sK0 ◇ X0) X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42123 sK0 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42123 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ (X4 ◇ X0)))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42123 X0 X1 X0 X0]
  have l6 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ X0) ◇ X1) = (X2 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 X0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) (X0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← l5 X1 (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l5 X0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← l1 X0 sK0 X1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 X1]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1]; rw [← l12 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l13 y z x]

@[equational_result]
theorem Equation41_implies_Equation42125 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42125 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK3)]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0 sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_42125_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42125 : Equation42125 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X1 X0 X4 X5 : G, (X2 ◇ X3) = ((X1 ◇ (X0 ◇ (X4 ◇ X5))) ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X3 X1 X0 X4 X5
    conv => enter [1]; rw [h42125 X2 X3 (X1 ◇ (X0 ◇ (X4 ◇ X5))) X5]
    conv => enter [1, 2, 2, 2]; rw [← h42125 X0 X1 X5 X4]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = ((X3 ◇ X2) ◇ (X0 ◇ X1)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h42125 X1 X2 (X3 ◇ X2) X0]
    conv => enter [1, 2]; rw [← h42125 X0 X1 X2 X3]
  have l2 : ∀ X2 X0 X1 X4 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X0 X1 X4 X3
    conv => enter [1]; rw [h42125 X2 (X0 ◇ X1) X4 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X3 X2 (X0 ◇ X1)]
  have l4 : ∀ X2 X3 X1 X0 X4 X5 : G, (X2 ◇ X3) = (X1 ◇ ((X0 ◇ (X4 ◇ X5)) ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X2 X3 X1 X0 X4 X5
    conv => enter [1]; rw [l0 X2 X3 X1 X0 X4 X5]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X4 ◇ X5)) (X3 ◇ (X2 ◇ (X0 ◇ X1)))]
  have l5 : ∀ X2 X3 X0 X4 X5 : G, (X2 ◇ X3) = (X2 ◇ ((X0 ◇ (X4 ◇ X5)) ◇ X3)) := by
    intro X2 X3 X0 X4 X5
    conv => enter [1]; rw [l4 X2 X3 X2 X0 X4 X5]
    conv => enter [1]; rw [← l2 X2 (X0 ◇ (X4 ◇ X5)) X3 X2 X0]
  have l6 : ∀ X2 X3 X0 X4 X5 : G, (X2 ◇ X3) = (X2 ◇ (X0 ◇ ((X4 ◇ X5) ◇ X3))) := by
    intro X2 X3 X0 X4 X5
    conv => enter [1]; rw [l5 X2 X3 X0 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X4 ◇ X5) X3]
  have l7 : ∀ X3 X0 X2 : G, (X3 ◇ X0) = (X2 ◇ X3) := by
    intro X3 X0 X2
    conv => enter [1]; rw [l3 X3 X0 X2 (X3 ◇ X3)]
    conv => enter [1]; rw [← l6 X2 X3 X0 X3 X3]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l7 sK0 sK0 X0]
    conv => enter [1]; rw [l7 X0 sK0 X1]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation42126 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42126 G := by
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
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h41 sK0 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK0 sK2 sK1]
  have l5 : ∀ sK0 sK3 sK2 sK1 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3 sK2 sK1
    conv => enter [1]; rw [h41 sK0 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK3 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

theorem Equation4512_42126_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42126 : Equation42126 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42126 sK0 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X4 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h42126 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ (X4 ◇ X4)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h42126 X0 X1 X0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0 X0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) (X0 ◇ X0) sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42126 X0 X1 (X1 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [l4 (X1 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
  intro x y z
  conv => enter [1]; rw [← l5 y z x]

@[equational_result]
theorem Equation41_implies_Equation42127 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42127 G := by
  have l0 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l1 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK1 ◇ sK0)]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l1 sK2 sK3 sK1 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]

theorem Equation4512_42127_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42127 : Equation42127 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X4 ◇ X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h42127 X0 X1 (X2 ◇ X3) X4 X5]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ (X4 ◇ X5)))]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X1 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l0 X0 X1 X0 X3 X0 X0]
    conv => enter [1]; rw [← h42127 X1 X3 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation41_implies_Equation42128 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42128 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x z (y ◇ (y ◇ (x ◇ x)))]

theorem Equation4512_42128_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42128 : Equation42128 G) : Equation41 G := by
  have l0 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X1 ◇ (X0 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← h42128 X0 X1 X2]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42128 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42128 X0 X1 X0]
  have l3 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l0 X2 X1 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3)) = (X1 ◇ X3) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l3 X2 X1 X0 X3]
    conv => enter [1]; rw [← l2 X1 X3 X0]
  have l5 : ∀ X1 X0 X3 : G, ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X3) = (X1 ◇ X3) := by
    intro X1 X0 X3
    conv => enter [1]; rw [l2 (X1 ◇ (X1 ◇ (X0 ◇ X0))) X3 X1]
    conv => enter [1]; rw [l4 X1 X1 X0 X3]
  have l6 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X3)) := by
    intro X1 X3 X0
    conv => enter [1]; rw [← l5 X1 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X0)) X3]
  have l7 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = ((X1 ◇ (X0 ◇ X0)) ◇ X3) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l6 X1 X3 X0]
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ X0)) X3 X1]
  have l8 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X1 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l7 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X3]
  have l9 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l8 X1 X3 X0]
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X3 X1]
  have l10 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l9 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l11 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X0 ◇ X3) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l10 X1 X3 X0]
    conv => enter [1]; rw [← l2 X0 X3 X0]
  have l12 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h42128 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [l11 X2 (X1 ◇ X1) X0]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l12 X1 X2 X1 X0]
    conv => enter [1]; rw [← l2 X2 (X0 ◇ (X1 ◇ X1)) X1]
  have l14 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l13 X1 X2 X0]
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X1) X2]
  have l15 : ∀ X1 X2 : G, (X1 ◇ X2) = (X1 ◇ X1) := by
    intro X1 X2
    conv => enter [1]; rw [l14 X1 X2 X1]
    conv => enter [1]; rw [← l2 X1 X1 X1]
  have l16 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK2]
    conv => enter [1, 2]; rw [l11 sK0 sK2 sK1]
  have l17 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l15 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l16 sK0 sK2 sK0]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK2]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

@[equational_result]
theorem Equation41_implies_Equation42130 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42130 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42130_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42130 : Equation42130 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = ((sK0 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42130 sK0 X1 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ X1) = ((sK2 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [h42130 sK1 X1 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h42130 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h42130 X1 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h42130 X0 X1 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l6 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ X1) = (sK2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l2 sK1 X1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0)))]
  have l7 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (sK0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l8 : ∀ sK1 X1 sK2 : G, (sK1 ◇ X1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 X1 sK2
    conv => enter [1]; rw [l6 sK1 X1 sK2 sK1]
    conv => enter [1, 2]; rw [← h42130 (sK1 ◇ sK2) X1 sK1]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l7 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← h42130 (sK0 ◇ sK0) X1 sK0]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) X1]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← h42130 sK0 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l13 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l15 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l14 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l9 sK0 (X0 ◇ X1)]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l17 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1, 2]; rw [← l17 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l17 sK0 X0]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l5 X0 sK0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l26 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l17 sK0 X1]
    conv => enter [1]; rw [l25 sK0 X1 X0]
  have l27 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l8 sK1 (sK1 ◇ sK2) sK2]
  have l28 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l27 sK2 sK0 sK1]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l28 sK1 sK2 sK0]
  have l30 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h42130 (sK1 ◇ sK2) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l29 sK0 sK1 sK2]
  have l31 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l30 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l17 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l32 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l31 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l26 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l33 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l32 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l15 sK0 (sK1 ◇ sK2) sK0]
  have l34 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l33 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l17 sK0 (sK1 ◇ sK2)]
  have l35 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h42130 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l34 sK1 sK2 (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2)))) sK0]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l34 sK1 sK2 (sK1 ◇ sK2) sK0]
  have l37 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l35 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [← l36 sK0 X0 X0]
  intro x y z
  conv => enter [1]; rw [← l37 y z x]

@[equational_result]
theorem Equation41_implies_Equation42131 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42131 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42131_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42131 : Equation42131 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X2 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h42131 (sK0 ◇ sK0) X1 X2 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h42131 X1 X2 X3 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h42131 X0 X1 X2 X1]
  have l3 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h42131 sK0 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h42131 X0 X1 X1 X2]
    conv => enter [1]; rw [← h42131 X1 X1 X2 (X0 ◇ X2)]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42131 sK0 X1 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 X1 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 X0]
    conv => enter [1]; rw [← l2 X0 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X1) = (X2 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h42131 X0 X1 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 X0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 X0 sK0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) X1 X0 X1]
  have l9 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [h42131 X0 (sK0 ◇ sK0) X2 X1]
    conv => enter [1, 2]; rw [← l5 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1))]
  have l10 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X1) ◇ sK0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l9 X0 sK0 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) sK0 X0 (sK0 ◇ sK0)]
  have l11 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l10 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 X0 sK0 sK0]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [← l5 sK0 X1]
  have l14 : ∀ X1 sK0 X3 X0 X2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X3 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X2)))) := by
    intro X1 sK0 X3 X0 X2
    conv => enter [1]; rw [h42131 X1 (sK0 ◇ sK0) X3 X2]
    conv => enter [1, 2]; rw [← l8 X0 ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) sK0]
  have l15 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = ((X1 ◇ X2) ◇ X0) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [l14 X1 sK0 X1 X0 X2]
    conv => enter [1]; rw [← l2 (X1 ◇ X2) X0 X1 (sK0 ◇ sK0)]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [l13 (sK0 ◇ sK0) sK2 sK0]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l8 (X1 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l15 X1 sK0 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 X0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [l13 (sK0 ◇ sK0) X0 sK0]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l16 sK1 sK2 sK0]
    conv => enter [1]; rw [← l19 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l20 y z x]

@[equational_result]
theorem Equation41_implies_Equation42132 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42132 G := by
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
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42132_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42132 : Equation42132 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h42132 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ X0))]
    conv => enter [1]; rw [← h42132 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h42132 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42132 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l2 sK0 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h42132 X0 X1 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) (sK0 ◇ X0) sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X1 ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [← l6 X1 sK0 X0]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l11 X0 X1 sK0]
    conv => enter [1]; rw [l11 X1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation42134 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42134 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_42134_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42134 : Equation42134 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42134 X0 X1 X0]
    conv => enter [1]; rw [← h42134 X2 X1 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42134 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [l1 sK0 X1 (X1 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation42135 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation42135 G := by
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
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_42135_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42135 : Equation42135 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X2 ◇ X1) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h42135 X0 X1 X1 X3]
    conv => enter [1]; rw [← h42135 X2 X1 X3 (X1 ◇ X3)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h42135 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42135 X2 X1 X0 X0]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h42135 sK0 sK0 X1 X2]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l3 sK0 X1 X2]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ X2)]
  have l5 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l4 sK0 X1 X2]
    conv => enter [1, 2]; rw [l0 sK0 X2]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK1 sK2]
  have l8 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← l1 X1 (sK0 ◇ sK0) (sK0 ◇ X0) X2]
    conv => enter [1, 2]; rw [l0 sK0 X0]
  have l9 : ∀ sK0 X2 X0 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ X0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l5 sK0 sK0 X0]
    conv => enter [1]; rw [← l8 X2 sK0 X0 sK0]
  have l10 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ X1) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l9 sK0 sK0 X1]
    conv => enter [1]; rw [l1 sK0 sK0 X1 X2]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

end Semigroup5
