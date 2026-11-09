import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation476_4512_implies_Equation5 (G : Type*) [Magma G] (h476 : Equation476 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h476 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h476 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h476 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h476 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2, 2]; rw [l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [← h476 X0 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h476 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← h476 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l6 (sK1 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h476 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h476 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation5_implies_Equation479 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation479 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation479_4512_implies_Equation5 (G : Type*) [Magma G] (h479 : Equation479 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h479 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h479 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) = X1 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 (X1 ◇ (X2 ◇ (X3 ◇ X1))) X2]
    conv => enter [1]; rw [← h479 X1 X2 X3]
  have l3 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h479 (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h479 sK0 X1 sK1]
  have l4 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((X1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l3 sK0 X1 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (X1 ◇ (sK1 ◇ sK0)) (X0 ◇ sK0)]
  have l5 : ∀ sK0 X1 sK1 : G, sK0 = (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l2 sK0 sK0 (X1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l4 sK0 X1 sK1 sK0]
  have l6 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h479 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 X0 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation5_implies_Equation483 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation483 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation483_4512_implies_Equation5 (G : Type*) [Magma G] (h483 : Equation483 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h483 (X0 ◇ X0) X1 X0]
    conv => enter [1, 2]; rw [← h483 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X1)))) = X1 := by
    intro X2 X1 X3 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h483 X1 X2 X3]
  have l2 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h483 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK0 X1 sK1 X0 X2 : G, (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) ◇ (X2 ◇ sK0))) := by
    intro sK0 X1 sK1 X0 X2
    conv => enter [1]; rw [h483 (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) X1 sK1]
  have l4 : ∀ sK0 X1 sK1 X0 X2 : G, (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((X1 ◇ (sK1 ◇ sK0)) ◇ (X2 ◇ sK0)))) := by
    intro sK0 X1 sK1 X0 X2
    conv => enter [1]; rw [l3 sK0 X1 sK1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 sK0 (X1 ◇ (sK1 ◇ sK0)) (X2 ◇ sK0)]
  have l5 : ∀ sK0 X1 sK1 : G, sK0 = (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l1 sK0 sK0 (X1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l4 sK0 X1 sK1 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation5_implies_Equation487 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation487 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation487_4512_implies_Equation5 (G : Type*) [Magma G] (h487 : Equation487 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h487 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))]
    conv => enter [1]; rw [← h487 X2 (X0 ◇ X1) X3]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
  have l3 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l0 X0 X2 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation491 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation491 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation491_4512_implies_Equation5 (G : Type*) [Magma G] (h491 : Equation491 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h491 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h491 (X0 ◇ X0) X1 X0]
  have l1 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h491 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [l0 sK1 (sK1 ◇ sK0)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l3 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2]; rw [l2 X0 (X1 ◇ X2) X1]
    conv => enter [1]; rw [← h491 X2 X3 X1]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h491 (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 X1 sK1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) (X1 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation5_implies_Equation495 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation495 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation495_4512_implies_Equation5 (G : Type*) [Magma G] (h495 : Equation495 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h495 X0 (X2 ◇ X0) X1 X2]
    conv => enter [1]; rw [← h495 (X2 ◇ X0) X1 X0 X1]
  have l1 : ∀ sK0 X1 sK1 X0 X2 : G, (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) ◇ (X2 ◇ sK0))) := by
    intro sK0 X1 sK1 X0 X2
    conv => enter [1]; rw [h495 (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) X0 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h495 sK0 sK0 X1 sK1]
  have l2 : ∀ sK0 X1 sK1 X0 X2 : G, (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((X1 ◇ (sK1 ◇ sK0)) ◇ (X2 ◇ sK0)))) := by
    intro sK0 X1 sK1 X0 X2
    conv => enter [1]; rw [l1 sK0 X1 sK1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 sK0 (X1 ◇ (sK1 ◇ sK0)) (X2 ◇ sK0)]
  have l3 : ∀ sK0 X1 sK1 : G, sK0 = (sK0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [h495 sK0 sK0 (X1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l2 sK0 X1 sK1 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h495 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation503 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation503 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation503_4512_implies_Equation5 (G : Type*) [Magma G] (h503 : Equation503 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [h503 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l0 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l1 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h503 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h503 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h503 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK1 ◇ sK0) ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l9 sK1 sK0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK0) X0]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  have l16 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) X0]
  have l17 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l16 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK1 ◇ sK0) ◇ sK1) X0]
  have l18 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l17 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [l15 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h503 (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l15 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0 ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 ((sK1 ◇ sK0) ◇ sK1) (sK1 ◇ sK1)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 (sK1 ◇ sK1)]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2]; rw [← l18 sK1 (sK1 ◇ sK1) sK0]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l29 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1 sK1]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h503 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l26 sK1 sK0]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK1) sK1]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l34 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l30 sK1 sK0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 sK1]
    conv => enter [1]; rw [← l35 sK1 sK0]
  have l37 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1, 2]; rw [← l36 sK0 sK1]
  have l38 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l39 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l40 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h503 X0 sK1]
    conv => enter [1]; rw [← l39 sK1 (sK1 ◇ (X0 ◇ (sK1 ◇ X0))) sK0]
    conv => enter [1]; rw [← h503 X0 sK1]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l40 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l42 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l40 sK1 sK0 sK0]
    conv => enter [1]; rw [← l41 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l42 x y]

@[equational_result]
theorem Equation5_implies_Equation506 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation506 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation506_4512_implies_Equation5 (G : Type*) [Magma G] (h506 : Equation506 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h506 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h506 X0 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h506 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h506 sK0 (sK1 ◇ sK0) sK1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h506 X0 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h506 X0 (X0 ◇ (X1 ◇ X0)) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation5_implies_Equation510 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation510 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [h5 (sK0 ◇ sK0) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation510_4512_implies_Equation5 (G : Type*) [Magma G] (h510 : Equation510 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h510 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h510 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h510 X0 X0]
  have l3 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h510 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h510 X0 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l7 X0]
    conv => enter [1]; rw [← h510 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 y x]

@[equational_result]
theorem Equation5_implies_Equation516 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation516 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [h5 (sK2 ◇ sK0) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation516_4512_implies_Equation5 (G : Type*) [Magma G] (h516 : Equation516 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X1 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h516 X0 X2 X1]
    conv => enter [1]; rw [← h516 (X1 ◇ X0) X2 X2]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2]; rw [l0 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h516 X2 X3 X1]
  have l2 : ∀ sK0 X1 X0 sK1 : G, sK0 = (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [h516 sK0 X1 sK1]
    conv => enter [1, 2, 2]; rw [l0 X1 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK0 X2 X0 X1 sK1 : G, sK0 = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 X2 (X0 ◇ X1) sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation5_implies_Equation520 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation520 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation520_4512_implies_Equation5 (G : Type*) [Magma G] (h520 : Equation520 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h520 (X0 ◇ X0) X1 X1]
    conv => enter [1, 2]; rw [← h520 X0 X1 (X0 ◇ X0)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l0 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1]; rw [← h520 X1 X2 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X1) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l1 X2 X0 X1]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l2 X2 X0 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h520 X1 X1 X0]
    conv => enter [1]; rw [l3 X2 X0 X1]
  have l5 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h520 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 sK1]
  have l6 : ∀ sK0 X1 sK1 : G, sK0 = (X1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l5 sK0 sK0 X1 sK1]
    conv => enter [1]; rw [l4 sK0 sK0 (X1 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation5_implies_Equation524 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation524 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation524_4512_implies_Equation5 (G : Type*) [Magma G] (h524 : Equation524 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h524 (X0 ◇ (sK1 ◇ sK0)) sK1 sK1]
    conv => enter [1, 2, 2]; rw [← h524 sK0 sK1 X0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l0 X0 sK1 sK0]
    conv => enter [1]; rw [← l0 X1 sK1 sK0]
  have l2 : ∀ sK1 sK0 X1 X2 X0 : G, (sK1 ◇ sK0) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X1 X2 X0
    conv => enter [1]; rw [h524 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 sK1 sK0 X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK1 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h524 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation5_implies_Equation532 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation532 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation532_4512_implies_Equation5 (G : Type*) [Magma G] (h532 : Equation532 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ sK0 X2 X0 X1 sK1 : G, sK0 = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [h532 sK0 X2 (X0 ◇ X1) sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← h532 (sK1 ◇ sK0) sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation537 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation537 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation537_4512_implies_Equation5 (G : Type*) [Magma G] (h537 : Equation537 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h537 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X3 : G, (X0 ◇ X3) = X3 := by
    intro X0 X3
    conv => enter [1, 2]; rw [h537 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation541 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation541 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation541_4512_implies_Equation5 (G : Type*) [Magma G] (h541 : Equation541 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h541 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h541 X0 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l0 X0 sK0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 (X1 ◇ (X2 ◇ (X3 ◇ X2))) X3]
    conv => enter [1]; rw [← h541 X2 X3 X1]
  have l4 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X0 ◇ ((X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h541 (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h541 sK0 sK1 X1]
  have l5 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l4 X1 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l6 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l5 X1 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
  have l7 : ∀ sK1 sK0 X1 : G, (sK1 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X1
    conv => enter [1, 2]; rw [← l3 sK1 X1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l6 X1 sK0 sK1 sK1]
  have l8 : ∀ sK0 X1 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 X1]
  have l9 : ∀ sK1 sK0 X1 : G, (sK1 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X1 sK1]
  have l10 : ∀ sK1 sK0 X1 X0 : G, (sK1 ◇ sK0) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l9 sK1 sK0 X1]
    conv => enter [1, 2]; rw [l1 sK0 (sK1 ◇ sK0) X0]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h541 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 sK0]
  have l12 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h541 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK1 sK0 X0]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK0)]
  have l15 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l10 sK1 sK0 sK0 (sK1 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1 sK1 sK1]
  have l17 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l18 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK0) X0]
  have l19 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK0 sK1]
    conv => enter [1]; rw [← l18 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l19 x y]

@[equational_result]
theorem Equation5_implies_Equation545 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation545 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation545_4512_implies_Equation5 (G : Type*) [Magma G] (h545 : Equation545 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h545 (X0 ◇ (X2 ◇ X0)) X1 X2]
    conv => enter [1, 2, 2]; rw [← h545 X0 (X0 ◇ (X2 ◇ X0)) X2]
  have l1 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h545 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l0 (sK1 ◇ sK0) sK0 sK1]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h545 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h545 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l4 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h545 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l2 X1 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK0) sK0 sK1]
  have l6 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← l5 sK0 sK1 X0]
    conv => enter [1]; rw [l5 sK0 sK1 X1]
  have l7 : ∀ sK0 X1 X2 X0 sK1 : G, sK0 = (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 X2 X0 sK1
    conv => enter [1]; rw [l4 sK0 X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [l6 sK0 sK1 sK0 X0]
  have l8 : ∀ X2 sK0 sK1 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ ((X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro X2 sK0 sK1 X0 X1
    conv => enter [1]; rw [h545 (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 X1 X2 sK1]
  have l9 : ∀ X2 sK0 sK1 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro X2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 X2 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l10 : ∀ X2 sK0 sK1 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))))) := by
    intro X2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 X2 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
  have l11 : ∀ X2 sK0 sK1 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l10 X2 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0 sK1 sK0]
  have l12 : ∀ X0 sK0 X2 sK1 : G, (X0 ◇ sK0) = (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 X2 sK1
    conv => enter [1, 2]; rw [l7 sK0 X0 X2 sK0 sK1]
    conv => enter [1]; rw [← l11 X2 sK0 sK1 X0 X0]
  have l13 : ∀ sK1 sK0 X2 : G, (sK1 ◇ sK0) = (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [l12 sK1 sK0 X2 sK1]
  have l14 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l13 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation5_implies_Equation549 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation549 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation549_4512_implies_Equation5 (G : Type*) [Magma G] (h549 : Equation549 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = (X3 ◇ X0) := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h549 X0 X1 (X3 ◇ X0) X3]
    conv => enter [1]; rw [← h549 (X3 ◇ X0) X1 X1 X0]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2]; rw [l0 X0 (X1 ◇ X2) X2]
    conv => enter [1]; rw [← h549 X2 X3 X4 X1]
  have l2 : ∀ X2 sK0 sK1 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ ((X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro X2 sK0 sK1 X0 X1
    conv => enter [1]; rw [h549 (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h549 sK0 X2 X2 sK1]
  have l3 : ∀ X2 sK0 sK1 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro X2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 X2 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l4 : ∀ sK0 X2 sK1 : G, sK0 = (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X2 sK1
    conv => enter [1]; rw [← l1 sK0 sK0 X2 (sK0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK1 sK0 sK0]
  have l5 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h549 (sK1 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 (sK1 ◇ sK0) sK1]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h549 (sK0 ◇ (sK1 ◇ sK0)) X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h549 sK0 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0 sK1 sK0 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation5_implies_Equation554 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation554 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation554_4512_implies_Equation5 (G : Type*) [Magma G] (h554 : Equation554 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h554 (X0 ◇ X0) X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h554 X0 (X0 ◇ X0) X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 X1 X2]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 (X1 ◇ (X2 ◇ (X3 ◇ X3))) X2]
    conv => enter [1]; rw [← h554 X3 X2 X1]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h554 X3 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X3 : G, (X0 ◇ X3) = X3 := by
    intro X0 X3
    conv => enter [1, 2]; rw [← l2 X0 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [l3 X0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [← l4 y x]

@[equational_result]
theorem Equation5_implies_Equation558 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation558 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation558_4512_implies_Equation5 (G : Type*) [Magma G] (h558 : Equation558 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h558 (X1 ◇ (X1 ◇ X0)) X1 X2]
    conv => enter [1, 2, 2]; rw [← h558 X0 X1 X1]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h558 (sK1 ◇ (sK1 ◇ sK0)) sK1 X0]
    conv => enter [1, 2, 2]; rw [← h558 sK0 sK1 sK1]
  have l2 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h558 (X1 ◇ sK0) sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK1 sK0 X1]
  have l3 : ∀ sK1 sK0 X1 : G, (sK1 ◇ sK0) = (X1 ◇ sK0) := by
    intro sK1 sK0 X1
    conv => enter [1, 2]; rw [h558 sK0 sK1 sK1]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 sK1]
  have l4 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h558 X3 X2 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X3)))]
    conv => enter [1]; rw [← h558 X3 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ X3)]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X3)))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [l0 X1 X3 (X0 ◇ X1)]
    conv => enter [1]; rw [l6 X0 X1 X2 X3]
  have l8 : ∀ X0 X3 : G, (X0 ◇ X3) = X3 := by
    intro X0 X3
    conv => enter [1, 2]; rw [← l4 X0 X0 X0 X3]
    conv => enter [1]; rw [l7 X0 X0 X0 X3]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation5_implies_Equation566 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation566 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, sK1 = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
  have l1 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation566_4512_implies_Equation5 (G : Type*) [Magma G] (h566 : Equation566 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = (X3 ◇ X0) := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h566 X0 X1 X1 X3]
    conv => enter [1]; rw [← h566 (X3 ◇ X0) X1 X1 X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X4 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l0 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X2]
    conv => enter [1]; rw [← h566 X4 X2 X1 X3]
  have l2 : ∀ sK0 X2 X1 X0 sK1 : G, sK0 = (X2 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X2 X1 X0 sK1
    conv => enter [1]; rw [h566 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l0 X0 (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) X2]
  have l3 : ∀ sK0 X2 X3 X0 X1 sK1 : G, sK0 = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X2 X3 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 (X2 ◇ X3) X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation5_implies_Equation571 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation571 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation571_4512_implies_Equation5 (G : Type*) [Magma G] (h571 : Equation571 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h571 (X0 ◇ X0) X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h571 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [l0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [← h571 X0 X1 X2]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h571 X0 X1 X0]
    conv => enter [1]; rw [l2 X1 X1 X0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation579 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation579 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2, 2]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation579_4512_implies_Equation5 (G : Type*) [Magma G] (h579 : Equation579 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X1 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h579 X0 X1 X1]
    conv => enter [1]; rw [← h579 (X1 ◇ X0) X2 X1]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [l0 X0 (X1 ◇ (X1 ◇ X2)) X1]
    conv => enter [1]; rw [← h579 X2 X3 X1]
  have l2 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h579 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK0 sK1 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation5_implies_Equation583 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation583 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK1) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation583_4512_implies_Equation5 (G : Type*) [Magma G] (h583 : Equation583 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = (X3 ◇ X0) := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h583 X0 X1 X1 X3]
    conv => enter [1]; rw [← h583 (X3 ◇ X0) X1 X1 X1]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [l0 X0 (X1 ◇ (X2 ◇ X3)) X1]
    conv => enter [1]; rw [← h583 X3 X4 X1 X2]
  have l2 : ∀ sK0 X2 X0 X1 sK1 : G, sK0 = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [h583 sK0 X2 (X0 ◇ X1) sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation5_implies_Equation588 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation588 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation588_4512_implies_Equation5 (G : Type*) [Magma G] (h588 : Equation588 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h588 X0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h588 (X0 ◇ X0) X1 X1 X1]
  have l1 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1)))) = X1 := by
    intro X2 X3 X4 X0 X1
    conv => enter [1, 2, 2, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h588 X1 X2 X3 X4]
  have l2 : ∀ sK0 X0 X1 X2 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h588 sK0 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK1 sK0]
  have l3 : ∀ sK0 X2 X3 X0 X1 sK1 : G, sK0 = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X2 X3 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 (X2 ◇ X3) X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation5_implies_Equation593 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation593 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation593_4512_implies_Equation5 (G : Type*) [Magma G] (h593 : Equation593 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h593 X0 X2 X1 X1]
    conv => enter [1]; rw [← h593 (X2 ◇ X0) X1 X2 X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X4 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l0 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X3]
    conv => enter [1]; rw [← h593 X4 X3 X1 X2]
  have l2 : ∀ sK0 sK1 X2 X0 X1 : G, sK0 = (sK1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [h593 sK0 sK1 (X2 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation5_implies_Equation598 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation598 G := by
  have l0 : ∀ sK1 sK0 sK3 : G, sK1 = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK3 sK1 sK2 : G, (sK0 ◇ (sK3 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation598_4512_implies_Equation5 (G : Type*) [Magma G] (h598 : Equation598 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = (X3 ◇ X0) := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h598 X0 X1 X3 X1]
    conv => enter [1]; rw [← h598 (X3 ◇ X0) X1 X1 X3]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [l0 X0 (X1 ◇ (X2 ◇ X3)) X2]
    conv => enter [1]; rw [← h598 X3 X4 X2 X1]
  have l2 : ∀ sK0 X2 sK1 X0 X1 : G, sK0 = (X2 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X2 sK1 X0 X1
    conv => enter [1]; rw [h598 sK0 X2 sK1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation5_implies_Equation603 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation603 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation603_4512_implies_Equation5 (G : Type*) [Magma G] (h603 : Equation603 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = (X3 ◇ X0) := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h603 X0 X1 X3 X3]
    conv => enter [1]; rw [← h603 (X3 ◇ X0) X1 X1 X3]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2]; rw [l0 X0 (X1 ◇ X2) X1]
    conv => enter [1]; rw [← h603 X2 X3 X4 X1]
  have l2 : ∀ sK0 X0 X1 X2 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h603 sK0 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l0 X2 sK0 sK1]
  have l3 : ∀ sK0 X2 X3 X0 X1 sK1 : G, sK0 = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X2 X3 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 (X2 ◇ X3) X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation5_implies_Equation608 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation608 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, sK2 = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK1]
  have l1 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK2)) sK4]
    conv => enter [1]; rw [h5 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK3]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 : G, sK2 = (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

theorem Equation608_4512_implies_Equation5 (G : Type*) [Magma G] (h608 : Equation608 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ sK0 X2 X3 X0 X1 sK1 : G, sK0 = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X2 X3 X0 X1 sK1
    conv => enter [1]; rw [h608 sK0 (X2 ◇ X3) X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← h608 (sK1 ◇ sK0) sK0 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation4898 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4898 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [h5 sK0 sK0]
    conv => enter [1, 2, 2, 2]; rw [h5 sK0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (x ◇ (x ◇ x)))) y]

theorem Equation4512_4898_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4898 : Equation4898 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4898 X0 (X1 ◇ X2)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4898 X0 X1]
    conv => enter [1]; rw [l0 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation4901 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4901 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [h5 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (x ◇ (y ◇ x)))) y]

theorem Equation4512_4901_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4901 : Equation4901 G) : Equation5 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4901 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) X2]
    conv => enter [1, 1]; rw [← h4901 X0 X1]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4901 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l8 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l7 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l8 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) sK1]
    conv => enter [1, 2, 2, 2]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4901 (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [l10 sK1 sK0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l10 sK1 sK0]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1)))]
  have l16 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l17 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l14 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) X0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1)))]
  have l19 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l17 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) X0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1)))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1)))]
  have l21 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l19 sK1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1))))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 sK1 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [← l21 sK1 (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1)))) sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1))]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1)))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 ((sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 sK1 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) (sK1 ◇ sK1)]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK1)))))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) (sK1 ◇ sK1)]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))))))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 (sK1 ◇ sK1)]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l6 sK1 (sK1 ◇ sK1) (sK1 ◇ sK0)]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← l6 sK1 sK1 sK1]
  have l31 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2]; rw [l30 sK1 sK0]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4901 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [l30 sK1 sK0]
  have l33 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l30 sK1 sK0]
  have l34 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l33 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1)))]
  have l36 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ X0))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) X0]
    conv => enter [1]; rw [l34 sK1 sK0 X0]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1)))]
  have l38 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 (sK1 ◇ sK0) sK1 X0]
    conv => enter [1]; rw [l36 sK1 sK0 X0]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1)))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [l38 sK1 sK0 (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))))]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1, 2]; rw [l38 sK1 sK0 ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) (sK1 ◇ sK1)]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 (sK1 ◇ sK1)]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l38 sK1 sK0 (sK1 ◇ sK1)]
  have l46 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4901 sK1 sK1]
    conv => enter [1]; rw [← l45 sK1 sK0]
  have l47 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l31 sK1 sK0]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4901 ((sK1 ◇ sK0) ◇ sK1) sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l46 sK1 sK0]
  have l49 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) X0]
  have l50 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l49 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 (((sK1 ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1))]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [← l50 sK1 (((sK1 ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) sK0]
  have l53 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [← l50 sK1 (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) sK0]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 sK1]
  have l56 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l55 sK1 sK0]
    conv => enter [1]; rw [← l50 sK1 sK1 sK0]
  have l57 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l58 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l57 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
  have l59 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l56 sK1 sK0]
  have l60 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 sK1]
  have l61 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l60 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
  have l62 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4901 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l61 sK1 sK0 sK0]
  have l63 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l64 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [← l58 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l64 x y]

@[equational_result]
theorem Equation5_implies_Equation4904 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4904 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [h5 (sK2 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (x ◇ (z ◇ x)))) y]

theorem Equation4512_4904_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4904 : Equation4904 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h4904 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4904 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation4908 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4908 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (y ◇ (x ◇ x)))) y]

theorem Equation4512_4908_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4908 : Equation4908 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4908 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK1 ◇ sK0) ◇ sK0) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2, 2]; rw [h4908 X0 sK0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ (X0 ◇ X0)))) sK1]
    conv => enter [1]; rw [← h4908 X0 sK0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4908 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [l5 sK1 sK0 (sK1 ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4908 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK1 sK0 (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4908 X0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = X0 := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 sK1 sK0 (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))]
    conv => enter [1]; rw [l5 sK1 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l9 sK0 sK0 X0]
    conv => enter [1]; rw [l10 sK0 sK0 X0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l11 sK0 X0]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [← l12 sK1 sK1 X0]
    conv => enter [1]; rw [l9 sK1 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l13 y x]

@[equational_result]
theorem Equation5_implies_Equation4911 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4911 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (y ◇ (y ◇ x)))) y]

theorem Equation4512_4911_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4911 : Equation4911 G) : Equation5 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4911 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4911 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 X0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 sK0 sK1]
  have l10 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) X0]
  have l11 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l11 sK1 sK0 X0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ X0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l12 sK1 sK0 X0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4911 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2, 2, 2]; rw [l5 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4911 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [l5 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1, 2]; rw [← l13 sK1 sK0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l4 sK0 (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l23 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4911 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l28 sK0 sK1]
  have l30 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l31 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) sK1]
  have l32 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l28 sK0 sK0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l32 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [← l30 sK0 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1, 2]; rw [← l34 sK1 sK0]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4911 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l35 sK0 sK1]
  have l37 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← l37 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) sK1]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [← l37 sK0 (sK0 ◇ sK0) sK1]
  have l40 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [← l39 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l40 x y]

@[equational_result]
theorem Equation5_implies_Equation4914 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4914 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (y ◇ (z ◇ x)))) y]

theorem Equation4512_4914_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4914 : Equation4914 G) : Equation5 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4914 (X0 ◇ (X1 ◇ (X2 ◇ X0))) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4914 X0 X1 X2]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h4914 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0))))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X0) ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X0)]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X0))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X0)))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X0) X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X2 X0 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [l2 X1 X2 X0 X0]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4914 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l9 (sK1 ◇ sK0) sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4914 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4914 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation5_implies_Equation4918 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4918 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (z ◇ (x ◇ x)))) y]

theorem Equation4512_4918_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4918 : Equation4918 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4918 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4918 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation4922 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4922 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (z ◇ (y ◇ x)))) y]

theorem Equation4512_4922_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4922 : Equation4922 G) : Equation5 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4922 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X0))))]
    conv => enter [1]; rw [← h4922 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation4926 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4926 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (z ◇ (z ◇ x)))) y]

theorem Equation4512_4926_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4926 : Equation4926 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h4926 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4926 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation4930 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4930 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK1]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ (z ◇ (w ◇ x)))) y]

theorem Equation4512_4930_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4930 : Equation4930 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h4930 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4930 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation4935 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4935 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (x ◇ (x ◇ x)))) y]

theorem Equation4512_4935_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4935 : Equation4935 G) : Equation5 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4935 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4935 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2, 2]; rw [h4935 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X0)))) sK1]
    conv => enter [1]; rw [← h4935 X0 sK0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4935 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l6 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0) X0]
  have l10 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l9 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l6 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4935 sK0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l12 sK0 sK0]
  have l15 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1, 2]; rw [l12 sK0 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l15 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l12 sK0 X0]
    conv => enter [1, 2]; rw [← l17 sK0 X0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l18 sK0 X0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l19 sK1 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [l18 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))]
  have l24 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK1 sK0 ((sK1 ◇ sK0) ◇ sK1)]
  have l25 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 ((sK1 ◇ sK0) ◇ sK1) sK1]
  have l26 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [l18 sK0 ((sK1 ◇ sK0) ◇ sK1)]
  have l27 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l28 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0 X0]
    conv => enter [1]; rw [l27 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l19 sK1 sK0 X0]
  have l29 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1]; rw [← l28 sK1 sK0 X0]
  have l30 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l29 sK0 X0 sK1]
    conv => enter [1]; rw [l18 sK0 X0]
  have l31 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l30 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l31 x y]

@[equational_result]
theorem Equation5_implies_Equation4938 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4938 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (x ◇ (y ◇ x)))) y]

theorem Equation4512_4938_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4938 : Equation4938 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK0 ◇ X0) ◇ (sK1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4938 (sK0 ◇ X0) sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4938 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l0 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (sK1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (sK1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))))]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
    conv => enter [1]; rw [← h4938 X0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, sK0 = (X0 ◇ (X0 ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4938 sK0 X0]
    conv => enter [1, 2]; rw [l7 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ sK0)))]
  have l9 : ∀ sK0 X0 : G, sK0 = (X0 ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2, 2]; rw [l7 sK0 (X0 ◇ sK0)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4938 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation5_implies_Equation4941 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4941 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (x ◇ (z ◇ x)))) y]

theorem Equation4512_4941_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4941 : Equation4941 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4941 (sK0 ◇ X0) X1 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4941 (X1 ◇ X0) X0 X0]
    conv => enter [1, 2]; rw [← h4941 X0 (X1 ◇ X0) X1]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h4941 X0 (X1 ◇ X2) X3]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0))))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l2 X1 X2 X0 X3]
  have l4 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l0 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l5 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l4 sK0 X0 X1 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation5_implies_Equation4945 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4945 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (y ◇ (x ◇ x)))) y]

theorem Equation4512_4945_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4945 : Equation4945 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4945 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK0) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2, 2]; rw [h4945 X0 sK0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ X0)))) sK1]
    conv => enter [1]; rw [← h4945 X0 sK0]
  have l6 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4945 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l5 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1 sK1]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l8 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h4945 X0 sK1]
    conv => enter [1]; rw [← l9 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4945 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l10 y x]

@[equational_result]
theorem Equation5_implies_Equation4948 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4948 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (y ◇ (y ◇ x)))) y]

theorem Equation4512_4948_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4948 : Equation4948 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h4948 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4948 X0 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h4948 X0 X0]
    conv => enter [1]; rw [← l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [h4948 (X0 ◇ X0) X0]
    conv => enter [1, 2, 2, 2]; rw [← l4 X0]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [← h4948 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l7 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4948 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 sK1 sK0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l8 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation5_implies_Equation4951 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4951 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (y ◇ (z ◇ x)))) y]

theorem Equation4512_4951_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4951 : Equation4951 G) : Equation5 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))) = X0 := by
    intro sK1 X0 sK0
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [← h4951 X0 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4951 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4951 ((sK1 ◇ sK0) ◇ sK1) sK1 sK1]
    conv => enter [1, 2, 2]; rw [l0 sK1 sK1 sK0]
  have l3 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h4951 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK1]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 sK1]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l3 sK1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l3 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l7 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← l6 sK1 ((sK1 ◇ sK0) ◇ sK1)]
  have l9 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0]
  have l10 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ X0) = X0 := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h4951 X0 sK1 sK1]
    conv => enter [1]; rw [← l6 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))))]
    conv => enter [1]; rw [← h4951 X0 sK1 sK1]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 (sK1 ◇ sK0) sK0]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [l11 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation5_implies_Equation4955 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4955 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (z ◇ (x ◇ x)))) y]

theorem Equation4512_4955_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4955 : Equation4955 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4955 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X0)))) = X0 := by
    intro sK1 X0 sK0
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4955 X0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l3 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [← h4955 (sK1 ◇ sK0) (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l5 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h4512 X0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l3 X0 sK1 sK0]
  have l6 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4955 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [l3 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) sK1 sK0]
  have l7 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [l3 (sK1 ◇ sK0) sK1 sK0]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l3 sK1 sK1 sK0]
  have l10 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l6 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l11 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X1)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l5 X0 sK1 sK0 X1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) X1]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 sK1 sK0 sK1]
  have l13 : ∀ sK1 sK0 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← l11 X0 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X1]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK1 sK0 X0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l17 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l3 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l16 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0 (sK1 ◇ sK0) sK1]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK1 sK0]
  have l21 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [l17 sK1 sK0 X0]
  have l22 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4955 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l21 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l25 x y]

@[equational_result]
theorem Equation5_implies_Equation4959 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4959 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (z ◇ (y ◇ x)))) y]

theorem Equation4512_4959_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4959 : Equation4959 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 X0 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4959 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4959 (sK1 ◇ sK0) (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4959 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation5_implies_Equation4963 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4963 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (z ◇ (z ◇ x)))) y]

theorem Equation4512_4963_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4963 : Equation4963 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4963 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4963 (sK1 ◇ sK0) (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4963 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4963 (sK1 ◇ sK0) sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4963 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 (sK1 ◇ sK0) sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation5_implies_Equation4967 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4967 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK1]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ (z ◇ (w ◇ x)))) y]

theorem Equation4512_4967_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4967 : Equation4967 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4967 (X1 ◇ X0) X0 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h4967 X0 (X1 ◇ X0) X1 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X2 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 X0]
  have l3 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) = X4 := by
    intro X1 X0 X2 X3 X4
    conv => enter [1, 2]; rw [l1 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X4]
    conv => enter [1]; rw [← h4967 X4 X1 X2 X3]
  have l4 : ∀ X2 X0 X1 X3 : G, (X2 ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X3 ◇ (X0 ◇ X0))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h4967 (X2 ◇ X0) X1 X3 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X0 X2 X2]
  have l5 : ∀ X2 X0 : G, (X2 ◇ X0) = X0 := by
    intro X2 X0
    conv => enter [1]; rw [l4 X2 X0 X2 X2]
    conv => enter [1]; rw [l3 X2 (X2 ◇ X0) X2 X0 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

@[equational_result]
theorem Equation5_implies_Equation4972 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4972 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (x ◇ (x ◇ x)))) y]

theorem Equation4512_4972_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4972 : Equation4972 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4972 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4972 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation4976 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4976 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (x ◇ (y ◇ x)))) y]

theorem Equation4512_4976_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4976 : Equation4976 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [h4976 (sK0 ◇ X0) sK1 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))))) = X2 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
    conv => enter [1]; rw [← h4976 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 : G, sK0 = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4976 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l3 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l0 sK0 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l4 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l3 sK0 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (X1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))))]
  have l5 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l4 sK0 X0 sK1 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) X0 sK0 sK0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l6 sK0 (sK1 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation5_implies_Equation4980 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4980 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (x ◇ (z ◇ x)))) y]

theorem Equation4512_4980_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4980 : Equation4980 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4980 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h4980 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4980 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation4984 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4984 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (x ◇ (w ◇ x)))) y]

theorem Equation4512_4984_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4984 : Equation4984 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h4984 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4984 X0 (X1 ◇ X0) (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0) X0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation4989 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4989 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (y ◇ (x ◇ x)))) y]

theorem Equation4512_4989_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4989 : Equation4989 G) : Equation5 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [← h4989 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4989 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation4993 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4993 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (y ◇ (y ◇ x)))) y]

theorem Equation4512_4993_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4993 : Equation4993 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 X0 : G, sK0 = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4993 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4993 (sK1 ◇ sK0) sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 sK1]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4993 ((sK1 ◇ sK0) ◇ sK0) sK1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK0) X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l5 sK1 sK0 X0]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l6 sK1 sK0 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4993 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l10 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← l9 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) sK1]
  have l11 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK0]
  have l12 : ∀ sK0 X0 X1 : G, sK0 = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4993 (sK1 ◇ sK0) sK0 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l11 sK0 sK1]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l15 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1]; rw [← l14 sK0 (X0 ◇ (sK0 ◇ sK0)) sK1]
  have l16 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK0 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation5_implies_Equation4997 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4997 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (y ◇ (z ◇ x)))) y]

theorem Equation4512_4997_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4997 : Equation4997 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4997 sK0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4997 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4997 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation5_implies_Equation5001 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5001 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, sK1 = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
  have l1 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK1]
  have l2 : ∀ sK1 sK3 sK2 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z y w]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (y ◇ (w ◇ x)))) y]

theorem Equation4512_5001_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5001 : Equation5001 G) : Equation5 G := by
  have l0 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X4 := by
    intro X2 X4 X0 X1 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5001 X4 X2 (X0 ◇ X1) X3]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5001 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X4 ◇ X0))))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X4 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0 X3 X4]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 (X1 ◇ X0) X0 X1 X1 X1]
    conv => enter [1]; rw [l2 X1 (X1 ◇ X0) X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5006 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5006 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (z ◇ (x ◇ x)))) y]

theorem Equation4512_5006_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5006 : Equation5006 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5006 X0 (X1 ◇ X2) X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5006 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5010 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5010 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK0) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z y]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (z ◇ (y ◇ x)))) y]

theorem Equation4512_5010_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5010 : Equation5010 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [h5010 (sK0 ◇ X0) sK1 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h5010 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l0 sK0 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l3 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l2 sK0 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h5010 X0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l4 sK0 (sK1 ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5010 (sK1 ◇ sK0) (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 (sK1 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK1 sK0 sK0]
  have l9 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation5_implies_Equation5014 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5014 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2, 2]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (z ◇ (z ◇ x)))) y]

theorem Equation4512_5014_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5014 : Equation5014 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5014 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h5014 (X0 ◇ X0) X1 X0]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5014 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5014 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1]
  have l3 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h5014 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation5_implies_Equation5018 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5018 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK1) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK1]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (z ◇ (w ◇ x)))) y]

theorem Equation4512_5018_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5018 : Equation5018 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5018 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5018 X0 (X1 ◇ X0) X0 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0) X0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5023 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5023 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (w ◇ (x ◇ x)))) y]

theorem Equation4512_5023_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5023 : Equation5023 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5023 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5023 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5028 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5028 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK1]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w y]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (w ◇ (y ◇ x)))) y]

theorem Equation4512_5028_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5028 : Equation5028 G) : Equation5 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X4 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5028 X4 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X0))))]
    conv => enter [1]; rw [← h5028 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X0))))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l1 X1 X2 X0 X3 X4]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0 X1 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

@[equational_result]
theorem Equation5_implies_Equation5033 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5033 G := by
  have l0 : ∀ sK1 sK0 sK3 : G, sK1 = (sK0 ◇ (sK3 ◇ sK1)) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h5 sK1 sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ (sK3 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK3 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1))) sK1]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (w ◇ (z ◇ x)))) y]

theorem Equation4512_5033_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5033 : Equation5033 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5033 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5033 X0 (X1 ◇ X0) X1 X0]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0) X0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5038 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5038 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1]; rw [h5 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x z w]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (w ◇ (w ◇ x)))) y]

theorem Equation4512_5038_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5038 : Equation5038 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X0))))]
    conv => enter [1]; rw [← h5038 X0 (X1 ◇ X2) X3 X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5038 X0 (X1 ◇ X0) X1 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0) X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5043 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5043 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, sK2 = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK1]
  have l1 : ∀ sK1 sK0 sK2 sK4 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK4
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK2)) sK4]
    conv => enter [1]; rw [h5 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK2]
  have l2 : ∀ sK2 sK4 sK1 sK0 : G, sK2 = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK4]
  intro x y z w u
  conv => enter [1]; rw [l2 x z w u]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ (w ◇ (u ◇ x)))) y]

theorem Equation4512_5043_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5043 : Equation5043 G) : Equation5 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 X5 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4 X5
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [← h5043 X0 (X1 ◇ X2) X3 X4 X5]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5043 X0 (X1 ◇ X0) X1 X1 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0) X0 X1 X1 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation5049 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5049 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1, 2]; rw [h5 (x ◇ (x ◇ (x ◇ x))) y]

theorem Equation4512_5049_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5049 : Equation5049 G) : Equation5 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5049 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1, 2]; rw [← h5049 X0 sK0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 X0]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0)))) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h5049 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) sK1]
    conv => enter [1]; rw [← h5049 X0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h5049 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [l7 sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [l9 sK0 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l11 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l9 sK0 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l19 : ∀ sK0 X0 : G, sK0 = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h5049 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l23 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l19 sK0 (sK1 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l25 x y]

@[equational_result]
theorem Equation5_implies_Equation5052 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5052 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1, 2]; rw [h5 (x ◇ (x ◇ (y ◇ x))) y]

theorem Equation4512_5052_implies_Equation5 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5052 : Equation5052 G) : Equation5 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5052 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5052 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) sK1]
    conv => enter [1, 2, 2, 2]; rw [l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l5 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l9 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l10 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l8 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) X0]
  have l11 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l10 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ sK1) X0]
  have l12 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l11 sK1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5052 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 sK1 sK0]
  have l14 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l15 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l14 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l17 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l15 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK1) (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l19 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l17 sK1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 X0]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK1 sK1 (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK1 (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) sK0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK1 sK1 sK0]
  have l26 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1 sK1]
    conv => enter [1, 2]; rw [l25 sK1 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5052 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [l25 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 sK0 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK0]
  have l34 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5052 sK1 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l35 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h5052 sK1 sK1]
    conv => enter [1, 2, 2]; rw [← l26 sK1]
  have l36 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1, 2]; rw [← l35 sK1]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l36 sK1]
    conv => enter [1]; rw [← l25 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l36 sK1]
  have l38 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1]; rw [l37 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5052 (sK0 ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l38 sK1 sK0]
  have l40 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l41 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l40 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1, 2]; rw [← l41 sK1 ((sK0 ◇ sK1) ◇ sK1) sK0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK1)]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l36 sK1]
  have l47 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l34 sK1 sK0]
  have l48 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1, 2]; rw [← l46 sK0 sK1]
  have l49 : ∀ sK1 sK0 : G, sK1 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l50 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l51 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h5052 X0 sK1]
    conv => enter [1]; rw [← l50 sK1 (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ X0)))) sK0]
    conv => enter [1]; rw [← h5052 X0 sK1]
  have l52 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l51 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l53 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l54 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [l51 sK1 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l54 x y]

@[equational_result]
theorem Equation5_implies_Equation5055 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation5055 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1, 2]; rw [h5 (x ◇ (x ◇ (z ◇ x))) y]

end Semigroup5
