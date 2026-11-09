import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation41671_implies_Equation41600 (G : Type*) [Magma G] (h41671 : Equation41671 G) : Equation41600 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41671 X1 X2 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41671 X0 X1 X1 X1 X1]
  intro x y z w
  conv => enter [1]; rw [l0 x x x]
  conv => enter [1]; rw [← l0 y x x]
  conv => enter [1]; rw [h41671 y y x z w]

theorem Equation4512_41671_implies_Equation41604 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41671 : Equation41671 G) : Equation41604 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41671 X1 X2 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41671 X0 X1 X1 X1 X1]
  have l2 : ∀ sK1 X2 X0 X1 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [h41671 sK1 X2 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [l0 sK1 (X0 ◇ X1)]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41671 (sK1 ◇ sK1) sK1 sK1 sK1 sK1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41671 X1 X1 (X1 ◇ (X1 ◇ X1)) X1 X1]
    conv => enter [1]; rw [← l1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l1 X0 sK1 sK1]
  have l6 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ X0) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [l1 X0 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK3 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [l4 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ X2)) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l1 sK1 X1 X2]
  have l9 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l8 sK1 X1 sK1]
  have l10 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l11 : ∀ sK3 sK1 sK0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK3 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK1 (sK1 ◇ sK0)]
  have l12 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK1 sK3]
    conv => enter [1]; rw [← l11 sK3 sK1 sK0]
  have l13 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK3 sK0]
  have l14 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 sK3 sK0]
  have l15 : ∀ sK3 sK1 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [← l6 sK3 sK3 sK1 sK0]
    conv => enter [1]; rw [h41671 sK3 X0 X1 sK1 sK0]
  have l16 : ∀ sK1 X0 X1 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 X1 sK3 sK0
    conv => enter [1]; rw [l14 sK1 sK3 sK0]
    conv => enter [1]; rw [l15 sK3 sK1 sK0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l16 x y x z w]

theorem Equation4512_41671_implies_Equation41608 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41671 : Equation41671 G) : Equation41608 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41671 X1 X2 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41671 X0 X1 X1 X1 X1]
  have l2 : ∀ sK1 X2 X0 X1 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [h41671 sK1 X2 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [l0 sK1 (X0 ◇ X1)]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41671 (sK1 ◇ sK1) sK1 sK1 sK1 sK1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41671 X1 X1 (X1 ◇ (X1 ◇ X1)) X1 X1]
    conv => enter [1]; rw [← l1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l1 X0 sK1 sK1]
  have l6 : ∀ X0 sK3 sK2 sK0 : G, (X0 ◇ X0) = ((sK3 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro X0 sK3 sK2 sK0
    conv => enter [1]; rw [l1 X0 sK3 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK3 (sK2 ◇ sK0) (sK2 ◇ sK0)]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [l4 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ X2)) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l1 sK1 X1 X2]
  have l9 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l8 sK1 X1 sK1]
  have l10 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l11 : ∀ sK3 sK2 sK0 sK1 : G, ((sK3 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK3 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK1 (sK2 ◇ sK0)]
  have l12 : ∀ sK1 sK3 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK3 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK1 sK3]
    conv => enter [1]; rw [← l11 sK3 sK2 sK0 sK1]
  have l13 : ∀ sK1 sK3 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK3 sK2 sK0]
  have l14 : ∀ sK1 sK3 sK2 sK0 : G, (sK1 ◇ sK1) = ((sK3 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 sK3 sK2 sK0]
  have l15 : ∀ sK3 sK2 sK0 X0 X1 : G, ((sK3 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK2 sK0 X0 X1
    conv => enter [1]; rw [← l6 sK3 sK3 sK2 sK0]
    conv => enter [1]; rw [h41671 sK3 X0 X1 sK2 sK0]
  have l16 : ∀ sK1 X0 X1 sK3 sK2 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 X0 X1 sK3 sK2 sK0
    conv => enter [1]; rw [l14 sK1 sK3 sK2 sK0]
    conv => enter [1]; rw [l15 sK3 sK2 sK0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l16 x y x z y w]

@[equational_result]
theorem Equation41671_implies_Equation41668 (G : Type*) [Magma G] (h41671 : Equation41671 G) : Equation41668 G := by
  intro x y z w
  conv => enter [1]; rw [h41671 x y z w y]

theorem Equation4512_41671_implies_Equation41709 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41671 : Equation41671 G) : Equation41709 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41671 (sK1 ◇ sK0) X0 X1 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 X2 sK1 X0 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X2 sK1 X0 X1
    conv => enter [1]; rw [h41671 sK0 X2 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [l1 sK1 sK0 (X0 ◇ X1)]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41671 (sK1 ◇ sK0) sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 sK1 sK1 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41671 sK1 sK1 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK1 sK0 sK1 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h41671 sK0 X0 X1 sK1 sK0]
  have l11 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [l10 sK1 sK0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_41671_implies_Equation41708 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41671 : Equation41671 G) : Equation41708 G := by
  have l0 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ sK3) ◇ ((sK0 ◇ (sK1 ◇ sK3)) ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3)))) ◇ X0) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK3) (sK0 ◇ (sK1 ◇ sK3)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK3 (sK0 ◇ (sK1 ◇ sK3))]
  have l1 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ sK3) ◇ ((sK0 ◇ (sK1 ◇ sK3)) ◇ X0)) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) X0]
  have l2 : ∀ sK1 sK3 X1 X2 sK0 X0 : G, ((sK1 ◇ sK3) ◇ (sK1 ◇ sK3)) = (X1 ◇ (X2 ◇ (sK1 ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) ◇ X0)))) := by
    intro sK1 sK3 X1 X2 sK0 X0
    conv => enter [1]; rw [h41671 (sK1 ◇ sK3) X1 X2 (sK0 ◇ (sK1 ◇ sK3)) X0]
    conv => enter [1, 2, 2]; rw [l1 sK1 sK3 sK0 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41671 X1 X2 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41671 X0 X1 X1 X1 X1]
  have l4 : ∀ sK1 sK3 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK3) ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3
    conv => enter [1]; rw [h41671 sK1 sK1 sK1 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK3))) sK1]
    conv => enter [1]; rw [← l2 sK1 sK3 sK1 sK1 sK1 sK1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41671 X1 X1 (X1 ◇ (X1 ◇ X1)) X1 X1]
    conv => enter [1]; rw [← l3 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l6 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ X0) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [l3 X0 sK3 (sK0 ◇ (sK1 ◇ sK3))]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK1 ◇ sK3)) (sK0 ◇ (sK1 ◇ sK3))]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1]; rw [l5 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X1 X2 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ X2)) := by
    intro sK1 X1 X2
    conv => enter [1]; rw [l3 sK1 X1 X2]
  have l9 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) ◇ (sK0 ◇ (sK1 ◇ sK3))) = (sK3 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK1 ◇ sK3)) (sK0 ◇ (sK1 ◇ sK3))]
    conv => enter [1, 2]; rw [l7 (sK0 ◇ (sK1 ◇ sK3)) sK1]
  have l10 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l8 sK1 X1 sK1]
  have l11 : ∀ sK3 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK3))) ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l6 sK0 sK3 sK0 sK1]
    conv => enter [1]; rw [h41671 sK0 X0 X1 sK1 sK3]
  have l12 : ∀ sK3 sK1 X0 X1 sK0 : G, (sK3 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK3 sK1 X0 X1 sK0
    conv => enter [1]; rw [← l9 sK3 sK0 sK1]
    conv => enter [1]; rw [l11 sK3 sK0 sK1 X0 X1]
  have l13 : ∀ sK1 X0 X1 sK0 sK3 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 X0 X1 sK0 sK3
    conv => enter [1]; rw [l10 sK1 sK3]
    conv => enter [1]; rw [l12 sK3 sK1 X0 X1 sK0]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w z]

theorem Equation4512_41671_implies_Equation41685 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41671 : Equation41671 G) : Equation41685 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41671 X1 X2 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41671 X0 X1 X1 X1 X1]
  have l2 : ∀ sK1 X2 X0 X1 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [h41671 sK1 X2 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [l0 sK1 (X0 ◇ X1)]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41671 (sK1 ◇ sK1) sK1 sK1 sK1 sK1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h41671 X1 X1 (X1 ◇ (X1 ◇ X1)) X1 X1]
    conv => enter [1]; rw [← l1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [l4 (sK1 ◇ sK1) X0]
  have l6 : ∀ sK1 X0 X1 sK2 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 X0 X1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [h41671 sK2 X0 X1 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l6 x y z y w]

theorem Equation4512_41671_implies_Equation41602 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41671 : Equation41671 G) : Equation41602 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) X0]
  have l2 : ∀ sK0 sK1 X1 X2 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X1 X2 sK2 X0
    conv => enter [1]; rw [h41671 (sK0 ◇ sK1) X1 X2 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 sK2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41671 X1 X2 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41671 X0 X1 X1 X1 X1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41671 sK0 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK0 sK0 sK0 sK0]
  have l5 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41671 X0 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [← l3 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l3 X0 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l9 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l3 sK0 X1 X2]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l9 sK0 X1 sK0]
  have l11 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l10 sK0 sK2]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1]
  have l12 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l7 sK2 sK2 sK0 sK1]
    conv => enter [1]; rw [h41671 sK2 X0 X1 sK0 sK1]
  have l13 : ∀ sK0 X0 X1 sK2 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 X1 sK2 sK1
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
    conv => enter [1]; rw [l12 sK2 sK0 sK1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l13 x y x z y]

theorem Equation4512_41709_implies_Equation41578 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41709 : Equation41709 G) : Equation41578 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ ((X4 ◇ (X5 ◇ (X0 ◇ X5))) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h41709 X1 X2 X3 (X4 ◇ (X5 ◇ (X0 ◇ X5)))]
    conv => enter [1, 2, 2, 2]; rw [← h41709 X0 X1 X4 X5]
  have l1 : ∀ sK1 X1 X2 sK2 sK3 sK0 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) ◇ X0)))) := by
    intro sK1 X1 X2 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h41709 sK1 X1 X2 ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2)))) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← h41709 (X3 ◇ X4) X0 X1 X2]
    conv => enter [1]; rw [← h4512 X3 X4 (X3 ◇ X4)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41709 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ X4)))]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X3 ◇ X4))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X4 X2]
  have l5 : ∀ sK1 X1 X2 sK2 sK3 sK0 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) ◇ X0))))) := by
    intro sK1 X1 X2 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l1 sK1 X1 X2 sK2 sK3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) X0 ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) ◇ X0)]
  have l6 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l0 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X4 (X5 ◇ (X0 ◇ X5)) (X0 ◇ X0)]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK1 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) sK1 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK1]
  have l8 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ X5) ◇ (X0 ◇ X0)))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l6 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X5 (X0 ◇ X5) (X0 ◇ X0)]
  have l9 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X5 ◇ (X0 ◇ X0))))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l8 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X5 (X0 ◇ X0)]
  have l10 : ∀ X1 X2 X3 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X5 ◇ X0))))) := by
    intro X1 X2 X3 X5 X0
    conv => enter [1]; rw [l9 X1 X2 X3 X1 X5 X0]
    conv => enter [1, 2, 2]; rw [← l4 X5 X0 X1 X5 X0]
  have l11 : ∀ X1 X5 : G, (X1 ◇ X1) = (X5 ◇ X5) := by
    intro X1 X5
    conv => enter [1]; rw [l10 X1 X1 X1 X5 X1]
    conv => enter [1]; rw [← l3 X5 X1 X1 X5 X1]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [l11 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l13 : ∀ sK1 X0 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h41709 sK0 X0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l13 x x y z w]

theorem Equation4512_41709_implies_Equation41685 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41709 : Equation41709 G) : Equation41685 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ ((X4 ◇ (X5 ◇ (X0 ◇ X5))) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h41709 X1 X2 X3 (X4 ◇ (X5 ◇ (X0 ◇ X5)))]
    conv => enter [1, 2, 2, 2]; rw [← h41709 X0 X1 X4 X5]
  have l1 : ∀ sK1 X1 X2 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ ((sK1 ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X1 X2 X0
    conv => enter [1]; rw [h41709 sK1 X1 X2 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2)))) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← h41709 (X3 ◇ X4) X0 X1 X2]
    conv => enter [1]; rw [← h4512 X3 X4 (X3 ◇ X4)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41709 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ X4)))]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X3 ◇ X4))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X4 X2]
  have l5 : ∀ sK1 X1 X2 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro sK1 X1 X2 X0
    conv => enter [1]; rw [l1 sK1 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 X0 ((sK1 ◇ sK1) ◇ X0)]
  have l6 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l0 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X4 (X5 ◇ (X0 ◇ X5)) (X0 ◇ X0)]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← l3 (sK1 ◇ sK1) sK1 sK1 sK1 sK1]
  have l8 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ X5) ◇ (X0 ◇ X0)))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l6 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X5 (X0 ◇ X5) (X0 ◇ X0)]
  have l9 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X5 ◇ (X0 ◇ X0))))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l8 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X5 (X0 ◇ X0)]
  have l10 : ∀ X1 X2 X3 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X5 ◇ X0))))) := by
    intro X1 X2 X3 X5 X0
    conv => enter [1]; rw [l9 X1 X2 X3 X1 X5 X0]
    conv => enter [1, 2, 2]; rw [← l4 X5 X0 X1 X5 X0]
  have l11 : ∀ X1 X5 : G, (X1 ◇ X1) = (X5 ◇ X5) := by
    intro X1 X5
    conv => enter [1]; rw [l10 X1 X1 X1 X5 X1]
    conv => enter [1]; rw [← l3 X5 X1 X1 X5 X1]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [l11 (sK1 ◇ sK1) X0]
  have l13 : ∀ sK1 X0 sK3 sK2 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 X0 sK3 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h41709 sK0 X0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l13 x y z y w]

theorem Equation4512_41709_implies_Equation41607 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41709 : Equation41709 G) : Equation41607 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ ((X4 ◇ (X5 ◇ (X0 ◇ X5))) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h41709 X1 X2 X3 (X4 ◇ (X5 ◇ (X0 ◇ X5)))]
    conv => enter [1, 2, 2, 2]; rw [← h41709 X0 X1 X4 X5]
  have l1 : ∀ sK0 X1 X2 sK2 sK1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0)))) := by
    intro sK0 X1 X2 sK2 sK1 X0
    conv => enter [1]; rw [h41709 sK0 X1 X2 ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK2)) X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2)))) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← h41709 (X3 ◇ X4) X0 X1 X2]
    conv => enter [1]; rw [← h4512 X3 X4 (X3 ◇ X4)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41709 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ X4)))]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X3 ◇ X4))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X4 X2]
  have l5 : ∀ sK0 X1 X2 sK2 sK1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0))))) := by
    intro sK0 X1 X2 sK2 sK1 X0
    conv => enter [1]; rw [l1 sK0 X1 X2 sK2 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK2)) X0 ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0)]
  have l6 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l0 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X4 (X5 ◇ (X0 ◇ X5)) (X0 ◇ X0)]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l5 sK0 sK0 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l3 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK0 sK0 (sK2 ◇ (sK1 ◇ sK2)) sK0]
  have l8 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ X5) ◇ (X0 ◇ X0)))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l6 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X5 (X0 ◇ X5) (X0 ◇ X0)]
  have l9 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X5 ◇ (X0 ◇ X0))))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l8 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X5 (X0 ◇ X0)]
  have l10 : ∀ X1 X2 X3 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X5 ◇ X0))))) := by
    intro X1 X2 X3 X5 X0
    conv => enter [1]; rw [l9 X1 X2 X3 X1 X5 X0]
    conv => enter [1, 2, 2]; rw [← l4 X5 X0 X1 X5 X0]
  have l11 : ∀ X1 X5 : G, (X1 ◇ X1) = (X5 ◇ X5) := by
    intro X1 X5
    conv => enter [1]; rw [l10 X1 X1 X1 X5 X1]
    conv => enter [1]; rw [← l3 X5 X1 X1 X5 X1]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 (sK0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← l7 sK0 X0 X0]
  have l13 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h41709 sK1 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z y]

theorem Equation4512_41709_implies_Equation41667 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41709 : Equation41709 G) : Equation41667 G := by
  have l0 : ∀ sK1 X1 X2 sK0 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X1 X2 sK0 X0
    conv => enter [1]; rw [h41709 sK1 X1 X2 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ ((X4 ◇ (X5 ◇ (X0 ◇ X5))) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h41709 X1 X2 X3 (X4 ◇ (X5 ◇ (X0 ◇ X5)))]
    conv => enter [1, 2, 2, 2]; rw [← h41709 X0 X1 X4 X5]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X4) ◇ X2)))) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← h41709 (X3 ◇ X4) X0 X1 X2]
    conv => enter [1]; rw [← h4512 X3 X4 (X3 ◇ X4)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41709 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ X4)))]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X3 ◇ X4))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X2))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X4 X2]
  have l5 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ ((X5 ◇ (X0 ◇ X5)) ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X4 (X5 ◇ (X0 ◇ X5)) (X0 ◇ X0)]
  have l6 : ∀ sK1 X1 X2 sK0 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))))) := by
    intro sK1 X1 X2 sK0 X0
    conv => enter [1]; rw [l0 sK1 X1 X2 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) X0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l7 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ ((X0 ◇ X5) ◇ (X0 ◇ X0)))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l5 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X5 (X0 ◇ X5) (X0 ◇ X0)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK1 sK1 sK0 sK1]
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK0 ◇ sK1)) sK1 sK1 (sK0 ◇ sK1) sK1]
  have l9 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X5 ◇ (X0 ◇ X0))))))) := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [l7 X1 X2 X3 X4 X5 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X5 (X0 ◇ X0)]
  have l10 : ∀ X1 X2 X3 X5 X0 : G, (X1 ◇ X1) = (X2 ◇ (X3 ◇ (X5 ◇ (X0 ◇ (X5 ◇ X0))))) := by
    intro X1 X2 X3 X5 X0
    conv => enter [1]; rw [l9 X1 X2 X3 X1 X5 X0]
    conv => enter [1, 2, 2]; rw [← l4 X5 X0 X1 X5 X0]
  have l11 : ∀ X1 X5 : G, (X1 ◇ X1) = (X5 ◇ X5) := by
    intro X1 X5
    conv => enter [1]; rw [l10 X1 X1 X1 X5 X1]
    conv => enter [1]; rw [← l3 X5 X1 X1 X5 X1]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 sK1]
    conv => enter [1]; rw [l11 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l13 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h41709 sK0 X0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l13 x y z w]

theorem Equation4512_41600_implies_Equation41553 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41600 : Equation41600 G) : Equation41553 G := by
  have l0 : ∀ X5 X1 X2 X0 X3 X4 : G, (X5 ◇ X5) = ((X1 ◇ X2) ◇ (X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4)))))) := by
    intro X5 X1 X2 X0 X3 X4
    conv => enter [1]; rw [h41600 X5 (X1 ◇ X2) X1 X2]
    conv => enter [1, 2, 2]; rw [h41600 (X1 ◇ X2) X0 X3 X4]
  have l1 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X5)))) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [← h41600 (X1 ◇ (X2 ◇ X3)) X0 X4 X5]
    conv => enter [1]; rw [h41600 (X1 ◇ (X2 ◇ X3)) X1 X2 X3]
    conv => enter [1, 2]; rw [h41600 (X1 ◇ (X2 ◇ X3)) X0 X4 X5]
  have l2 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X5))))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X5)))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X3) (X0 ◇ (X4 ◇ X5))]
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X3) (X0 ◇ (X4 ◇ X5))]
  have l3 : ∀ X5 X1 X2 X0 X3 X4 : G, (X5 ◇ X5) = (X1 ◇ (X2 ◇ (X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4))))))) := by
    intro X5 X1 X2 X0 X3 X4
    conv => enter [1]; rw [l0 X5 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X5 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X4)))))]
  have l4 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X4 ◇ X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h41600 X0 X1 (X2 ◇ X3) (X0 ◇ (X4 ◇ X5))]
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4 X5]
  have l5 : ∀ X5 X1 X2 X0 X3 X4 : G, (X5 ◇ X5) = (X1 ◇ (X2 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))))))) := by
    intro X5 X1 X2 X0 X3 X4
    conv => enter [1]; rw [l3 X5 X1 X2 X0 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ X4))]
  have l6 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X5)))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l4 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 (X0 ◇ (X4 ◇ X5))]
  have l7 : ∀ X1 X5 : G, (X1 ◇ X1) = (X5 ◇ X5) := by
    intro X1 X5
    conv => enter [1]; rw [l5 X1 X5 X1 X1 X1 X1]
    conv => enter [1]; rw [← l6 X5 X1 X1 X1 X1 (X1 ◇ (X1 ◇ X1))]
  intro x y z w
  conv => enter [1]; rw [l7 x y]
  conv => enter [1]; rw [h41600 y x z w]

theorem Equation4512_41600_implies_Equation41685 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41600 : Equation41600 G) : Equation41685 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h41600 X1 sK1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41600 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41600 X0 X1 X1 X1]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41600 sK1 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ (X0 ◇ X1))]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 sK1 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) sK1 (sK1 ◇ sK1)]
  have l5 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [l2 X1 sK1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [h41600 (X0 ◇ (sK1 ◇ sK1)) X0 sK1 sK1]
    conv => enter [1, 2]; rw [l2 (X0 ◇ (sK1 ◇ sK1)) sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK1) sK1]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1, 2]; rw [← l7 sK1]
  have l9 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l5 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l7 sK1]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 sK1]
    conv => enter [1]; rw [← l9 X0 sK1 sK1]
  have l11 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [h41600 X0 sK2 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_41600_implies_Equation41674 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41600 : Equation41600 G) : Equation41674 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41600 X1 X2 X0 (X2 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41600 X0 X2 X1 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41600 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41600 X0 X1 X1 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41600 sK0 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l4 X0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l4 X0 sK2]
    conv => enter [1]; rw [l2 sK0 sK2 (sK2 ◇ sK2)]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 (sK0 ◇ sK2) sK0 sK2]
    conv => enter [1]; rw [← l8 sK0 X0 sK2]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← l13 sK0]
  have l15 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h41600 X0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l15 x y z z]

theorem Equation4512_41600_implies_Equation41684 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41600 : Equation41600 G) : Equation41684 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h41600 X1 sK1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41600 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41600 X0 X1 X1 X1]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41600 sK1 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ (X0 ◇ X1))]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 sK1 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) sK1 (sK1 ◇ sK1)]
  have l5 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [l2 X1 sK1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 (X0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [h41600 (X0 ◇ (sK1 ◇ sK1)) X0 sK1 sK1]
    conv => enter [1, 2]; rw [l2 (X0 ◇ (sK1 ◇ sK1)) sK1]
  have l7 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [l2 (sK1 ◇ sK1) sK1]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1, 2]; rw [← l7 sK1]
  have l9 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l5 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l7 sK1]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 sK1]
    conv => enter [1]; rw [← l9 X0 sK1 sK1]
  have l11 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [h41600 X0 sK2 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_41668_implies_Equation41685 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41685 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK1 ◇ X0) X2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 X0]
  have l2 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41668 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l0 sK1 (X0 ◇ X1)]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41668 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l5 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = (sK1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [l1 X1 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 sK1 X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))]
  have l6 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [l5 X1 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l2 sK1 X1 X1 X1 (sK1 ◇ sK1)]
  have l7 : ∀ X1 sK1 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l6 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ sK1) sK1]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [← l7 X0 sK1]
  have l10 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [h41668 sK2 sK2 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]

theorem Equation4512_41668_implies_Equation41602 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41602 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) X0]
  have l3 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK0 ◇ X0) X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l4 : ∀ X1 sK0 sK2 sK1 X0 X2 : G, (X1 ◇ X1) = (((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0))))) := by
    intro X1 sK0 sK2 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) X2 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l2 sK0 sK1 sK2 X0]
  have l5 : ∀ sK0 sK1 X0 X1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [h41668 (sK0 ◇ sK1) X0 X1 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l2 sK0 sK1 sK2 X0]
  have l6 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41668 sK0 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l5 sK0 sK1 sK0 sK0 sK0]
  have l8 : ∀ X1 sK0 sK2 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0)))))) := by
    intro X1 sK0 sK2 sK1 X0 X2
    conv => enter [1]; rw [l4 X1 sK0 sK2 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0 (X2 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0))))]
  have l9 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = (sK0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [l3 X1 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l10 : ∀ X1 sK0 sK2 sK1 : G, (X1 ◇ X1) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 sK2 sK1
    conv => enter [1]; rw [l8 X1 sK0 sK2 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l6 sK0 X1 X1 X1 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l11 : ∀ X1 sK0 : G, (X1 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l9 X1 sK0 X1 X1]
    conv => enter [1, 2]; rw [← l6 sK0 X1 X1 X1 (sK0 ◇ sK0)]
  have l12 : ∀ X1 sK0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l11 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l12 (sK0 ◇ sK0) sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [← l13 sK0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41668 X0 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l14 (X0 ◇ (X0 ◇ X1)) sK0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l15 sK0 X1 sK0]
  have l17 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l10 sK2 sK0 sK2 sK1]
    conv => enter [1]; rw [h41668 sK2 sK1 X0 sK0]
  have l18 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l17 sK0 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l18 x y x z]

theorem Equation4512_41668_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK1 ◇ X0) X2 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK1 X0]
  have l5 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l6 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41668 sK0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l8 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = (sK1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [l4 X1 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 sK1 X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))))]
  have l9 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [l8 X1 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l5 sK1 X1 X1 X1 (sK1 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ X1 sK1 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l9 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l11 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [l10 X1 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation4512_41668_implies_Equation41576 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41576 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l4 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK1 ◇ X0) X2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 X0]
  have l5 : ∀ X1 sK2 sK3 sK0 sK1 X0 X2 : G, (X1 ◇ X1) = (((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0))))) := by
    intro X1 sK2 sK3 sK0 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0) X2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l2 sK1 sK2 sK3 sK0 X0]
  have l6 : ∀ sK1 X1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 sK0 X0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK1) X1 sK0 X0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 (X0 ◇ X1)]
  have l7 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41668 sK1 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l6 sK1 sK1 sK1 sK1]
  have l9 : ∀ X1 sK2 sK3 sK0 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)))))) := by
    intro X1 sK2 sK3 sK0 sK1 X0 X2
    conv => enter [1]; rw [l5 X1 sK2 sK3 sK0 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0))))]
  have l10 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = (sK1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [l4 X1 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 sK1 X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))]
  have l11 : ∀ X1 sK2 sK3 sK0 sK1 : G, (X1 ◇ X1) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro X1 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l9 X1 sK2 sK3 sK0 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l7 sK1 X1 X1 X1 (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))]
  have l12 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [l10 X1 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l7 sK1 X1 X1 X1 (sK1 ◇ sK1)]
  have l13 : ∀ X1 sK1 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l12 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l14 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l13 (sK1 ◇ sK1) sK1]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [← l13 X0 sK1]
  have l16 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h41668 X0 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l15 (X0 ◇ (X0 ◇ X1)) sK1]
  have l17 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l16 sK1 X1 sK1]
  have l18 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [← l11 sK3 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [h41668 sK3 sK1 X0 sK0]
  have l19 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l17 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l18 sK1 sK3 sK0 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [l19 x y z w]

theorem Equation4512_41668_implies_Equation41585 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41585 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK1 ◇ X0) X2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l4 sK1 X0]
  have l6 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l7 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41668 sK0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h41668 (sK0 ◇ (sK1 ◇ sK1)) X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 (X0 ◇ X1)]
  have l9 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41668 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l4 sK1 (X0 ◇ X1)]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41668 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41668 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l13 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = (sK1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [l5 X1 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 sK1 X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))]
  have l14 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [l13 X1 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l6 sK1 X1 X1 X1 (sK1 ◇ sK1)]
  have l15 : ∀ X1 sK1 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l14 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [h41668 (sK0 ◇ sK0) sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l12 sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK1) sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41668 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0)]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK1) sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 (sK0 ◇ sK0)]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l22 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l24 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l15 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l27 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 1]; rw [l25 sK1 sK0]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1, 1]; rw [l25 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [l25 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l31 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1, 2]; rw [l33 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l35 x y]

theorem Equation4512_41668_implies_Equation41592 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41592 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l13 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41668 (sK0 ◇ sK1) X0 X1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l2 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41668 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0 sK0]
    conv => enter [1, 2, 2]; rw [l12 sK0 sK1]
  have l15 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h41668 (sK0 ◇ sK1) X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [l9 sK1 sK0 (X0 ◇ X1)]
  have l16 : ∀ sK1 X0 sK0 X1 X2 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (X1 ◇ (X0 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) := by
    intro sK1 X0 sK0 X1 X2
    conv => enter [1, 2]; rw [h41668 X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (X1 ◇ (X0 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))))]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41668 sK0 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l13 sK0 sK1 sK0 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [l21 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l24 x y]

theorem Equation4512_41668_implies_Equation41548 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41548 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l10 : ∀ X1 sK0 sK1 X0 X2 : G, (X1 ◇ X1) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))))) := by
    intro X1 sK0 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) X2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l8 sK1 sK0 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41668 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 sK1]
    conv => enter [1, 2, 2]; rw [l9 sK0 sK1]
  have l12 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l13 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41668 sK0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l14 : ∀ sK1 X1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 sK0 X0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK1) X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 (X0 ◇ X1)]
  have l15 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h41668 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l4 sK0 sK1 (X0 ◇ X1)]
  have l16 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41668 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l5 sK1 (X0 ◇ X1)]
  have l17 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h41668 (sK0 ◇ (sK1 ◇ sK1)) X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l8 sK1 sK0 (X0 ◇ X1)]
  have l18 : ∀ sK1 X0 sK0 X1 X2 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ (X0 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 X0 sK0 X1 X2
    conv => enter [1, 2]; rw [h41668 X0 (sK0 ◇ (sK1 ◇ sK1)) X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (X1 ◇ (X0 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0 sK1 sK0]
  have l20 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41668 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41668 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41668 (sK0 ◇ (sK1 ◇ sK1)) sK0 sK0 sK0]
    conv => enter [1]; rw [← l14 sK1 sK0 sK0 sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [← l18 sK1 sK0 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l25 : ∀ X1 sK0 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)))))) := by
    intro X1 sK0 sK1 X0 X2
    conv => enter [1]; rw [l10 X1 sK0 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))))]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [l21 sK1 sK0]
  have l27 : ∀ X1 sK0 sK1 : G, (X1 ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [l25 X1 sK0 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l12 sK1 X1 X1 X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l22 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [l28 sK1 sK0]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [l27 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ sK1)]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l31 sK1 sK0]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [h41668 (sK0 ◇ sK0) sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l23 sK0]
  have l35 : ∀ X2 sK0 X0 X1 X3 : G, (X2 ◇ X2) = (sK0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (sK0 ◇ sK0)) ◇ (X3 ◇ X0))))) := by
    intro X2 sK0 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 sK0 (X2 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h41668 (X2 ◇ (sK0 ◇ sK0)) X0 X1 X3]
  have l36 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41668 sK0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l37 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1, 2]; rw [← l23 sK0]
  have l38 : ∀ X2 sK0 X0 X1 X3 : G, (X2 ◇ X2) = (sK0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ (X3 ◇ X0)))))) := by
    intro X2 sK0 X0 X1 X3
    conv => enter [1]; rw [l35 X2 sK0 X0 X1 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (sK0 ◇ sK0) (X3 ◇ X0)]
  have l39 : ∀ X2 sK0 : G, (X2 ◇ X2) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X2 sK0
    conv => enter [1]; rw [l38 X2 sK0 X2 X2 X2]
    conv => enter [1, 2]; rw [← l12 (sK0 ◇ sK0) X2 X2 X2 X2]
  have l40 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l34 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l39 X2 sK0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l20 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [l41 sK1 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1, 2]; rw [l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1, 2]; rw [l44 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l45 x y]

@[equational_result]
theorem Equation41668_implies_Equation41550 (G : Type*) [Magma G] (h41668 : Equation41668 G) : Equation41550 G := by
  intro x y z
  conv => enter [1]; rw [h41668 x x y z]

theorem Equation4512_41668_implies_Equation41568 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41568 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK0 ◇ X0) X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l5 : ∀ X1 sK1 sK2 sK0 X0 X2 : G, (X1 ◇ X1) = (((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0))))) := by
    intro X1 sK1 sK2 sK0 X0 X2
    conv => enter [1]; rw [h41668 X1 ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l2 sK0 sK1 sK2 X0]
  have l6 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h41668 sK0 X1 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l3 sK1 sK0 (X0 ◇ X1)]
  have l7 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l9 : ∀ X1 sK1 sK2 sK0 X0 X2 : G, (X1 ◇ X1) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0)))))) := by
    intro X1 sK1 sK2 sK0 X0 X2
    conv => enter [1]; rw [l5 X1 sK1 sK2 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0 (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0))))]
  have l10 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = (sK0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [l4 X1 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l11 : ∀ X1 sK1 sK2 sK0 : G, (X1 ◇ X1) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro X1 sK1 sK2 sK0
    conv => enter [1]; rw [l9 X1 sK1 sK2 sK0 X1 X1]
    conv => enter [1, 2]; rw [← l7 sK0 X1 X1 X1 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))))]
  have l12 : ∀ X1 sK0 : G, (X1 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l10 X1 sK0 X1 X1]
    conv => enter [1, 2]; rw [← l7 sK0 X1 X1 X1 (sK0 ◇ sK0)]
  have l13 : ∀ X1 sK0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l12 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l13 (sK0 ◇ sK0) sK0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [← l14 sK0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41668 X0 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l15 (X0 ◇ (X0 ◇ X1)) sK0]
  have l17 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l16 sK0 X1 sK0]
  have l18 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l11 sK2 sK1 sK2 sK0]
    conv => enter [1]; rw [h41668 sK2 sK0 X0 sK1]
  have l19 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l17 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l18 sK1 sK2 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l19 x y z y]

theorem Equation4512_41668_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41621 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK0 ◇ X0) X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l8 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41668 (sK1 ◇ sK0) X0 X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK0 X0]
  have l9 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h41668 sK1 X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41668 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0 sK1]
    conv => enter [1, 2, 2]; rw [l6 sK0 sK1]
  have l11 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h41668 sK0 X1 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l3 sK1 sK0 (X0 ◇ X1)]
  have l12 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK0) X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 (X0 ◇ X1)]
  have l13 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l14 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (X2 ◇ sK0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X0 ◇ (X2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h41668 X0 sK0 X1 X2]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41668 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0 sK1]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK0 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l10 sK0 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l9 sK1 sK1 sK1 sK0]
  have l19 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = (sK0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [l7 X1 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l23 : ∀ X1 sK0 : G, (X1 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l19 X1 sK0 X1 X1]
    conv => enter [1, 2]; rw [← l13 sK0 X1 X1 X1 (sK0 ◇ sK0)]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l25 : ∀ X1 sK0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l23 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l26 : ∀ X1 sK1 sK0 : G, (X1 ◇ X1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [l25 X1 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l26 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l28 : ∀ sK1 sK0 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X1 X2
    conv => enter [1]; rw [← l26 (sK1 ◇ X1) sK1 sK0]
    conv => enter [1]; rw [h41668 (sK1 ◇ X1) X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [l26 (sK1 ◇ X1) sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l26 (sK0 ◇ sK0) sK1 sK0]
  have l30 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l29 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 sK0 X1 X2]
    conv => enter [1, 2, 2]; rw [← l29 sK0 sK0]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
  have l32 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [h41668 X0 sK1 X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l22 sK1 sK0]
  have l33 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l32 X0 sK1 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l29 sK0 sK1]
  have l34 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l33 X0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l30 sK0 X0 X0]
  have l35 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l34 X0 sK1 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l26 sK1 sK1 sK0]
    conv => enter [1]; rw [l35 sK1 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l36 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l37 x y]

theorem Equation4512_41668_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41547 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l3 : ∀ X1 sK0 X0 X2 sK1 : G, (X1 ◇ X1) = ((sK0 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0 X2 sK1
    conv => enter [1]; rw [h41668 X1 (sK0 ◇ X0) X2 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 sK0 X0]
  have l4 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41668 (sK1 ◇ sK0) X0 X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [l2 sK1 sK0 X0]
  have l5 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h41668 sK0 X1 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK1 sK0 (X0 ◇ X1)]
  have l6 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41668 sK1 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l9 : ∀ X1 sK0 X0 X2 sK1 : G, (X1 ◇ X1) = (sK0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0 X2 sK1
    conv => enter [1]; rw [l3 X1 sK0 X0 X2 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l11 : ∀ X1 sK0 sK1 : G, (X1 ◇ X1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [l9 X1 sK0 X1 X1 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 X1 X1 X1 (sK0 ◇ sK0)]
  have l12 : ∀ X1 sK0 sK1 : G, (X1 ◇ X1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [l11 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l10 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l12 (sK0 ◇ sK0) sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation4512_41668_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41557 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK0 ◇ X0) X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h41668 sK0 X1 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l1 sK1 sK0 (X0 ◇ X1)]
  have l4 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l6 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = (sK0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [l2 X1 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l7 : ∀ X1 sK0 : G, (X1 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l6 X1 sK0 X1 X1]
    conv => enter [1, 2]; rw [← l4 sK0 X1 X1 X1 (sK0 ◇ sK0)]
  have l8 : ∀ X1 sK0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l7 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l8 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l10 sK1 sK0]
    conv => enter [1]; rw [h41668 sK1 sK0 X0 sK1]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l12 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y y]

theorem Equation4512_41668_implies_Equation41538 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41538 G := by
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
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l3 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l6 sK1 X0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 sK1]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l5 sK1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l11 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = ((sK1 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK1 ◇ X0) X2 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK1 X0]
  have l12 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l13 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK1) X1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ X1)]
  have l14 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41668 sK0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l15 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41668 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l2 sK1 (X0 ◇ X1)]
  have l16 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK1) X1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [l10 sK1 (X0 ◇ X1)]
  have l17 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41668 (sK1 ◇ (sK1 ◇ sK1)) sK1 (sK1 ◇ sK1) sK1]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l19 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l13 sK1 X1 X0]
  have l20 : ∀ X1 sK1 X0 X2 : G, (X1 ◇ X1) = (sK1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))))) := by
    intro X1 sK1 X0 X2
    conv => enter [1]; rw [l11 X1 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 sK1 X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))))]
  have l21 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l17 sK1]
  have l22 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1 sK1 sK1]
    conv => enter [1]; rw [← l19 sK1 sK1 sK1]
  have l23 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [l20 X1 sK1 X1 X1]
    conv => enter [1, 2]; rw [← l12 sK1 X1 X1 X1 (sK1 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ X1 sK1 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l23 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l25 : ∀ X1 sK1 : G, (X1 ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [l24 X1 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
  have l26 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41668 X0 (sK0 ◇ sK0) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l18 sK0]
  have l27 : ∀ sK1 sK0 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← l25 X0 sK1]
    conv => enter [1]; rw [l26 X0 sK0 X1]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [h41668 (sK0 ◇ sK0) sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l18 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41668 sK0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41668 (sK1 ◇ (sK1 ◇ sK1)) sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41668 sK1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41668 X0 sK0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l33 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41668 X1 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [← h41668 X0 sK0 X1 sK0]
  have l34 : ∀ X1 sK0 sK1 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [l33 X1 sK0 X1]
    conv => enter [1, 2]; rw [l25 X1 sK1]
  have l35 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK0 sK1 X0]
    conv => enter [1]; rw [← l32 sK0 X0 sK1]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0)]
  have l37 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1, 2]; rw [← l18 sK0]
  have l38 : ∀ X1 sK0 sK1 : G, (X1 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [l34 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l25 sK1 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l31 sK1 sK0]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1]; rw [l36 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l25 sK1 sK1]
    conv => enter [1]; rw [l38 sK1 sK0 sK1]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [l41 sK1 sK0]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1, 1]; rw [← l42 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l44 sK1 sK0]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2, 1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
    conv => enter [1, 2]; rw [l40 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [l47 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [← l50 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l39 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l52 x y]
  conv => enter [1]; rw [l42 y x]

theorem Equation4512_41668_implies_Equation41628 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41628 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = (((sK0 ◇ sK0) ◇ X0) ◇ (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h41668 X1 ((sK0 ◇ sK0) ◇ X0) X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK0 X0]
  have l2 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41668 (sK0 ◇ sK0) X1 sK0 X0]
    conv => enter [1, 2]; rw [← l0 sK0 (X0 ◇ X1)]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41668 sK0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 sK0 sK0 sK0]
  have l5 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [l1 X1 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))))]
  have l6 : ∀ X1 sK0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [l5 X1 sK0 X1 X1]
    conv => enter [1, 2]; rw [← l2 (sK0 ◇ sK0) X1 X1 X1 sK0]
  have l7 : ∀ X1 sK0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l6 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l8 : ∀ X1 sK0 : G, (X1 ◇ X1) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l7 X1 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41668 X0 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l8 (X0 ◇ (X0 ◇ X1)) sK0]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l10 sK0 X1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_41668_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation41534 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = ((sK0 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK0 ◇ X0) X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l4 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41668 sK0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l6 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ X1) = (sK0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [l2 X1 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 (X2 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l7 : ∀ X1 sK0 : G, (X1 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l6 X1 sK0 X1 X1]
    conv => enter [1, 2]; rw [← l3 sK0 X1 X1 X1 (sK0 ◇ sK0)]
  have l8 : ∀ X1 sK0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l7 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41668 (sK1 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l8 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation4512_41668_implies_Equation53904 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation53904 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK2 ◇ sK2))]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l3 : ∀ X1 sK0 sK2 X0 X2 sK1 : G, (X1 ◇ X1) = (((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0))))) := by
    intro X1 sK0 sK2 X0 X2 sK1
    conv => enter [1]; rw [h41668 X1 ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) X2 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l1 sK0 sK1 sK2 X0]
  have l4 : ∀ X1 sK2 X0 X2 : G, (X1 ◇ X1) = ((sK2 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))))) := by
    intro X1 sK2 X0 X2
    conv => enter [1]; rw [h41668 X1 (sK2 ◇ X0) X2 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [l2 sK2 X0]
  have l5 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l6 : ∀ sK2 X1 X0 : G, (sK2 ◇ sK2) = (X1 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h41668 sK2 X1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (X0 ◇ X1)]
  have l7 : ∀ sK2 X1 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1)))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h41668 sK2 X1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l2 sK2 (X0 ◇ X1)]
  have l8 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ X1))) X4]
    conv => enter [1, 1]; rw [← h41668 X0 X1 X2 X3]
  have l9 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l8 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l10 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l7 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41668 (sK2 ◇ sK2) sK2 sK2 sK2]
  have l11 : ∀ X1 sK2 X0 X2 : G, (X1 ◇ X1) = (sK2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)))))) := by
    intro X1 sK2 X0 X2
    conv => enter [1]; rw [l4 X1 sK2 X0 X2]
    conv => enter [1]; rw [← h4512 sK2 X0 (X2 ◇ (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))))]
  have l12 : ∀ X1 sK0 sK2 X0 X2 sK1 : G, (X1 ◇ X1) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)))))) := by
    intro X1 sK0 sK2 X0 X2 sK1
    conv => enter [1]; rw [l3 X1 sK0 sK2 X0 X2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) X0 (X2 ◇ (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0))))]
  have l13 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l9 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ X1)) X4]
  have l14 : ∀ X1 sK2 : G, (X1 ◇ X1) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK2
    conv => enter [1]; rw [l11 X1 sK2 X1 X1]
    conv => enter [1, 2]; rw [← l5 sK2 X1 X1 X1 (sK2 ◇ sK2)]
  have l15 : ∀ X1 sK0 sK2 : G, (X1 ◇ X1) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 sK2
    conv => enter [1]; rw [l12 X1 sK0 sK2 X1 X1 X1]
    conv => enter [1, 2]; rw [← l5 sK0 X1 X1 X1 (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l16 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l13 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X3 ◇ X1) X4]
  have l17 : ∀ X1 sK2 : G, (X1 ◇ X1) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro X1 sK2
    conv => enter [1]; rw [l14 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
  have l18 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l16 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X1 X4]
  have l19 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l10 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l20 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l21 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
  have l22 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro sK2
    conv => enter [1]; rw [l10 sK2]
    conv => enter [1]; rw [l17 (sK2 ◇ sK2) sK2]
  have l23 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l22 sK2]
    conv => enter [1]; rw [← l17 X0 sK2]
  have l24 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l23 X0 sK2]
  have l25 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h41668 X0 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l23 (X0 ◇ (X0 ◇ X1)) sK2]
  have l26 : ∀ sK2 X1 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X1
    conv => enter [1]; rw [l25 sK2 X1 sK2]
  have l27 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1, 1]; rw [l26 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l28 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l26 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l19 sK0 sK2]
  have l29 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l26 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l20 sK1 sK0 sK2]
  have l30 : ∀ sK2 X0 X1 X2 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [l6 sK2 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK2 ◇ sK2) ◇ (X2 ◇ (X0 ◇ X1)))]
  have l31 : ∀ sK2 X1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X1
    conv => enter [1]; rw [l30 sK2 sK2 X1 sK2]
    conv => enter [1]; rw [← l18 (sK2 ◇ sK2) X1 sK2 X1 sK2]
  have l32 : ∀ sK2 X1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X1
    conv => enter [1]; rw [l31 sK2 X1]
    conv => enter [1]; rw [← l27 sK2 X1 (sK2 ◇ sK2)]
  have l33 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1, 1]; rw [l15 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK2)) (sK0 ◇ sK0) X1]
  have l34 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ X1))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l33 X0 X1 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X1]
  have l35 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l34 X0 X1 sK0 sK2]
    conv => enter [1, 2]; rw [l24 sK0 X1 sK2]
  have l36 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l35 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← l21 sK0 sK2 X1]
  have l37 : ∀ X0 X1 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l36 X0 X1 X0 sK2]
    conv => enter [1, 1]; rw [← l28 sK2 X0]
  have l38 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = ((X0 ◇ X0) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l32 sK2 X1]
    conv => enter [1]; rw [l37 sK2 X1 X0]
  have l39 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ sK2) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l38 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l39 x y z]
  conv => enter [1]; rw [l29 z y x]

theorem Equation4512_41668_implies_Equation53922 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation53922 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK2 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK1 ◇ sK2))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) X0]
  have l4 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l4 sK2 sK1]
  have l6 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l4 sK2 sK1]
  have l7 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l6 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) X0]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l8 sK1 sK2]
  have l10 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) X0]
  have l11 : ∀ X1 sK1 sK2 X0 X2 : G, (X1 ◇ X1) = (((sK1 ◇ sK2) ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0))))) := by
    intro X1 sK1 sK2 X0 X2
    conv => enter [1]; rw [h41668 X1 ((sK1 ◇ sK2) ◇ X0) X2 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l7 sK2 sK1 X0]
  have l12 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l13 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK2) X1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ sK2) (X0 ◇ X1)]
  have l14 : ∀ sK2 X1 sK0 sK1 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1)))) := by
    intro sK2 X1 sK0 sK1 X0
    conv => enter [1]; rw [h41668 sK2 X1 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2 (X0 ◇ X1)]
  have l15 : ∀ sK2 sK1 X1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)))) := by
    intro sK2 sK1 X1 sK0 X0
    conv => enter [1]; rw [h41668 (sK2 ◇ (sK1 ◇ sK2)) X1 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2 (X0 ◇ X1)]
  have l16 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h41668 (sK1 ◇ sK2) X1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [l10 sK1 sK2 (X0 ◇ X1)]
  have l17 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ X1))) X4]
    conv => enter [1, 1]; rw [← h41668 X0 X1 X2 X3]
  have l18 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l17 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l19 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← h41668 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK1 (sK1 ◇ sK2) sK1]
  have l20 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41668 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK1 sK1 sK1]
    conv => enter [1]; rw [← l15 sK2 sK1 sK1 sK1 sK1]
  have l21 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK2 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41668 (sK1 ◇ sK2) sK1 sK1 sK1]
    conv => enter [1]; rw [← l14 sK2 sK1 sK1 sK1 sK1]
  have l22 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l13 sK1 sK2 X1 X0]
  have l23 : ∀ X1 sK1 sK2 X0 X2 : G, (X1 ◇ X1) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0)))))) := by
    intro X1 sK1 sK2 X0 X2
    conv => enter [1]; rw [l11 X1 sK1 sK2 X0 X2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) X0 (X2 ◇ (X1 ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0))))]
  have l24 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l18 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ X1)) X4]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l19 sK1 sK2]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l21 sK1 sK2]
  have l27 : ∀ X1 sK1 sK2 : G, (X1 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [l23 X1 sK1 sK2 X1 X1]
    conv => enter [1, 2]; rw [← l12 sK2 X1 X1 X1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
  have l28 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l24 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X3 ◇ X1) X4]
  have l29 : ∀ X1 sK1 sK2 : G, (X1 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [l27 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l26 sK1 sK2]
  have l30 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l28 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X1 X4]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [l20 sK1 sK2]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [l29 (sK2 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l33 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) X0]
  have l34 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1, 1]; rw [l29 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) X1]
  have l35 : ∀ X0 X1 sK1 sK2 : G, ((X0 ◇ X0) ◇ X1) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l34 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l33 sK1 sK2 X1]
  have l36 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l35 X0 X1 sK1 sK2]
  have l37 : ∀ sK1 sK2 X0 X1 X2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l22 sK1 sK2 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X2 ◇ (X0 ◇ X1)))]
  have l38 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l37 sK1 sK2 sK1 X1 sK1]
    conv => enter [1]; rw [← l30 (sK2 ◇ (sK1 ◇ sK2)) X1 sK1 X1 sK1]
  have l39 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l38 sK1 sK2 X1]
    conv => enter [1]; rw [l36 (sK2 ◇ (sK1 ◇ sK2)) X1 sK1 sK2]
  have l40 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((X0 ◇ X0) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l39 sK1 sK2 X1]
    conv => enter [1]; rw [← l35 X0 X1 sK1 sK2]
  have l41 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l40 sK1 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l41 x y y z]

theorem Equation4512_41668_implies_Equation54273 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation54273 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ X1 sK2 X0 X2 sK1 : G, (X1 ◇ X1) = ((sK2 ◇ X0) ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))))) := by
    intro X1 sK2 X0 X2 sK1
    conv => enter [1]; rw [h41668 X1 (sK2 ◇ X0) X2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 sK2 X0]
  have l3 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l4 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41668 sK1 X1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l5 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41668 sK1 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l1 sK1 (X0 ◇ X1)]
  have l6 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ X1))) X4]
    conv => enter [1, 1]; rw [← h41668 X0 X1 X2 X3]
  have l7 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X1))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l6 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41668 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l9 : ∀ X1 sK2 X0 X2 sK1 : G, (X1 ◇ X1) = (sK2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)))))) := by
    intro X1 sK2 X0 X2 sK1
    conv => enter [1]; rw [l2 X1 sK2 X0 X2 sK1]
    conv => enter [1]; rw [← h4512 sK2 X0 (X2 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))))]
  have l10 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X1)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l7 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ X1)) X4]
  have l11 : ∀ X1 sK2 sK1 : G, (X1 ◇ X1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK2 sK1
    conv => enter [1]; rw [l9 X1 sK2 X1 X1 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 X1 X1 X1 (sK1 ◇ sK2)]
  have l12 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X1) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X3 ◇ X1) X4]
  have l13 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l12 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X1 X4]
  have l14 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l11 X0 sK2 sK1]
  have l15 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h41668 X0 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l11 (X0 ◇ (X0 ◇ X1)) sK2 sK1]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l11 (sK1 ◇ sK1) sK2 sK1]
  have l17 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l15 X0 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 X0]
  have l18 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l14 X0 X1 X0 sK1]
    conv => enter [1, 1]; rw [← l16 sK1 X0]
  have l19 : ∀ sK2 sK1 X1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [← l11 sK2 sK2 sK1]
    conv => enter [1]; rw [l17 sK2 X1 sK1]
  have l20 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l16 sK1 sK1]
    conv => enter [1]; rw [l19 sK1 sK1 X1]
  have l21 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l20 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l22 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l4 sK1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ sK1) ◇ (X2 ◇ (X0 ◇ X1)))]
  have l23 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l22 sK1 sK1 X1 sK1]
    conv => enter [1]; rw [← l13 (sK1 ◇ sK1) X1 sK1 X1 sK1]
  have l24 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X1
    conv => enter [1]; rw [l23 sK1 X1]
    conv => enter [1]; rw [← l21 sK1 X1 (sK1 ◇ sK1)]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l24 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l16 y x]
  conv => enter [1]; rw [← l25 z y x]

theorem Equation4512_41668_implies_Equation54243 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41668 : Equation41668 G) : Equation54243 G := by
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
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41668 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK2 ◇ sK2)) X0 sK0]
    conv => enter [1, 2, 2]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41668 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l11 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h41668 (sK0 ◇ sK1) X1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [l5 sK0 sK1 (X0 ◇ X1)]
  have l12 : ∀ sK2 X1 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1)))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h41668 sK2 X1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l6 sK2 (X0 ◇ X1)]
  have l13 : ∀ sK1 X0 sK2 X1 X2 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ (X2 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 X0 sK2 X1 X2
    conv => enter [1, 2]; rw [h41668 X0 (sK2 ◇ sK2) X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (X1 ◇ (X0 ◇ (X2 ◇ (sK2 ◇ sK2))))]
  have l14 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l12 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41668 (sK2 ◇ sK2) sK2 sK2 sK2]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h41668 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 (sK0 ◇ sK1) sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 (sK0 ◇ sK1) sK1 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l9 sK0 sK1 sK1 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l18 sK1 sK0]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l14 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l21 : ∀ X2 sK1 X0 X1 sK0 X3 : G, (X2 ◇ X2) = (sK1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (sK0 ◇ sK1)) ◇ (X3 ◇ X0))))) := by
    intro X2 sK1 X0 X1 sK0 X3
    conv => enter [1]; rw [h41668 X2 sK1 (X2 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [h41668 (X2 ◇ (sK0 ◇ sK1)) X0 X1 X3]
  have l22 : ∀ X2 sK1 X0 X1 sK0 X3 : G, (X2 ◇ X2) = (sK1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ (X3 ◇ X0)))))) := by
    intro X2 sK1 X0 X1 sK0 X3
    conv => enter [1]; rw [l21 X2 sK1 X0 X1 sK0 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (sK0 ◇ sK1) (X3 ◇ X0)]
  have l23 : ∀ X2 sK1 sK0 : G, (X2 ◇ X2) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X2 sK1 sK0
    conv => enter [1]; rw [l22 X2 sK1 X2 X2 sK0 X2]
    conv => enter [1, 2]; rw [← l10 (sK0 ◇ sK1) X2 X2 X2 X2]
  have l24 : ∀ X2 sK1 sK0 : G, (X2 ◇ X2) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro X2 sK1 sK0
    conv => enter [1]; rw [l23 X2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l25 : ∀ X2 sK0 sK1 : G, (X2 ◇ X2) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK0 sK1
    conv => enter [1]; rw [l24 X2 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l26 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41668 X0 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l25 (X0 ◇ (X0 ◇ X1)) sK0 sK1]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l25 (sK2 ◇ sK2) sK0 sK1]
    conv => enter [1]; rw [← l14 sK2]
  have l28 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l25 sK0 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 X1 sK0 sK1]
  have l29 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2]
    conv => enter [1, 2]; rw [← l27 sK0 sK1 sK2]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l29 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l30 z x y]

@[equational_result]
theorem Equation41613_implies_Equation41597 (G : Type*) [Magma G] (h41613 : Equation41613 G) : Equation41597 G := by
  intro x y z
  conv => enter [1]; rw [h41613 x y y z]

@[equational_result]
theorem Equation41613_implies_Equation41605 (G : Type*) [Magma G] (h41613 : Equation41613 G) : Equation41605 G := by
  intro x y z
  conv => enter [1]; rw [h41613 x y z y]

theorem Equation4512_41613_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (X2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41613 sK0 (X0 ◇ X1) X2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (X2 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41613 sK0 sK0 sK0 sK0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l3 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h41613 X1 X2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l2 sK0 (X0 ◇ X1) X1]
  have l4 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l3 X1 X1 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 (X0 ◇ X1) X1]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 X0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l5 X0 sK0]
    conv => enter [1]; rw [l4 X0 sK0 X1]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l5 X0 sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 X1 X0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l9 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation4512_41613_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation41621 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41613 (sK1 ◇ (sK0 ◇ sK0)) X0 X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK1 sK0]
  have l11 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41613 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0 X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK1 sK0]
  have l12 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h41613 X0 X1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l13 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41613 (sK0 ◇ sK0) X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 2, 2]; rw [l9 sK1 sK0]
  have l14 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ X3) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [h41613 X3 X4 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l15 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41613 (X1 ◇ X0) X2 X0 X1]
    conv => enter [1, 2]; rw [← h41613 X0 (X1 ◇ X0) X1 X1]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41613 sK0 (sK1 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ (X1 ◇ sK0))]
  have l17 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41613 (sK1 ◇ sK0) (sK1 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l3 sK1 sK0 (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))]
  have l18 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41613 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ X0)))]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41613 X0 X0 X0 X0]
  have l20 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l17 sK1 sK0 X0 X1]
  have l21 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l15 X1 X0 X2]
  have l22 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)]
  have l23 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l11 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)))]
  have l24 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l10 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK0) (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))]
  have l25 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X0]
    conv => enter [1]; rw [← l21 X1 X0 X0]
  have l26 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41613 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l22 sK0 sK0 sK0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 (sK1 ◇ sK0) sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l23 sK1 sK0 sK1 sK1]
  have l28 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l16 sK0 sK1 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l30 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l28 sK1 sK0 X0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) sK1 sK0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l30 sK0 sK0 X0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l31 sK1 sK0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l32 sK0 X0]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l36 sK1 sK0]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l39 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h41613 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0 sK0 sK1]
    conv => enter [1]; rw [← l39 sK1 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l41 x y]
  conv => enter [1]; rw [l38 y x]

theorem Equation4512_41613_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation41547 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l8 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41613 (sK1 ◇ (sK0 ◇ sK0)) X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41613 X0 X1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l10 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41613 (sK0 ◇ sK0) X0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK1 sK0]
  have l11 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41613 (X1 ◇ X0) X2 X0 X1]
    conv => enter [1, 2]; rw [← h41613 X0 (X1 ◇ X0) X1 X1]
  have l12 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41613 sK0 (sK1 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ (X1 ◇ sK0))]
  have l13 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41613 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [← l5 sK0 sK1 (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))]
  have l14 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41613 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ X0)))]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41613 X0 X0 X0 X0]
  have l16 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l13 sK1 sK0 X0 X1]
  have l17 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l11 X1 X0 X2]
  have l18 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l10 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK0]
  have l19 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l8 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK0) (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ sK0))]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X0]
    conv => enter [1]; rw [← l17 X1 X0 X0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l18 sK0 sK0 sK0]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l23 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l22 sK1 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l23 sK0 sK0 X0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l26 sK1 sK0]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41613 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK0]
    conv => enter [1]; rw [← l30 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l31 x y]
  conv => enter [1]; rw [l28 y x]

theorem Equation4512_41613_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation41557 G := by
  have l0 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (X2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41613 sK0 (X0 ◇ X1) X2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (X2 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41613 sK0 sK0 sK0 sK0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41613 sK0 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 (sK1 ◇ sK0) sK0]
  have l5 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h41613 X1 X2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l2 sK0 (X0 ◇ X1) X1]
  have l6 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l5 X1 X1 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 (X0 ◇ X1) X1]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 X0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l7 X0 sK0]
    conv => enter [1]; rw [l6 X0 sK0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l7 X0 sK0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l8 sK0 X1 X0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ sK0) sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1, 2]; rw [l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation4512_41613_implies_Equation41628 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation41628 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41613 sK0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l0 sK0 (X0 ◇ sK0)]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41613 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ sK0))]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_41613_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation41534 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h41613 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ X3) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [h41613 X3 X4 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l4 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41613 (X1 ◇ X0) X2 X0 X1]
    conv => enter [1, 2]; rw [← h41613 X0 (X1 ◇ X0) X1 X1]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41613 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ X0)))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41613 X0 X0 X0 X0]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l4 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l8 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (X1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X0]
    conv => enter [1]; rw [l7 X0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (X2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41613 sK0 (X0 ◇ X1) X2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (X2 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41613 sK0 sK0 sK0 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l15 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation4512_41613_implies_Equation53938 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation53938 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l5 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 X1 sK2 : G, (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)))) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [h41613 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) X0 X1 sK2]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK2 sK0 sK1]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41613 X0 X1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l8 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41613 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l4 sK0 sK1 (X0 ◇ (X1 ◇ sK1))]
  have l9 : ∀ sK0 sK1 X0 X1 sK2 : G, (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))))) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) (X1 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1))]
  have l10 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l11 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l10 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 (sK1 ◇ sK1) (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l11 X0 sK1 sK1]
  have l13 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [← l12 sK1 X1]
    conv => enter [1]; rw [l12 sK1 X0]
  have l14 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l12 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l15 : ∀ X0 sK1 X1 X2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1 X2
    conv => enter [1]; rw [l13 X0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l16 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l5 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [l13 (sK0 ◇ sK1) sK1 X0]
  have l17 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l16 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l14 sK1 sK2 sK2]
  have l18 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [l13 sK0 sK1 X1]
    conv => enter [1]; rw [← l15 X0 sK1 X1 X1]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l17 sK2 sK0 sK1]
  have l20 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l18 X1 sK0 sK1 sK0]
  have l21 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l22 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1 sK0]
    conv => enter [1, 1]; rw [← l20 sK0 sK1 sK0]
  have l24 : ∀ sK1 X2 X0 X1 : G, ((sK1 ◇ sK1) ◇ X2) = (X0 ◇ ((sK1 ◇ (X1 ◇ (sK1 ◇ sK1))) ◇ X2)) := by
    intro sK1 X2 X0 X1
    conv => enter [1, 1]; rw [h41613 sK1 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (X1 ◇ (sK1 ◇ sK1))) X2]
  have l25 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41613 sK1 (sK0 ◇ sK1) X0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1 sK1 sK1]
    conv => enter [1]; rw [← l14 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l27 : ∀ sK1 X2 X0 X1 : G, ((sK1 ◇ sK1) ◇ X2) = (X0 ◇ (sK1 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [l24 sK1 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (X1 ◇ (sK1 ◇ sK1)) X2]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1]; rw [l13 (sK1 ◇ sK1) sK1 sK0]
  have l29 : ∀ sK1 X2 X0 X1 : G, ((sK1 ◇ sK1) ◇ X2) = (X0 ◇ (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2)))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [l27 sK1 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK1 ◇ sK1) X2]
  have l30 : ∀ sK1 X2 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X2) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2))) := by
    intro sK1 X2 X0 sK0
    conv => enter [1]; rw [l29 sK1 X2 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l21 sK0 sK1 X2 sK1]
  have l31 : ∀ sK1 X2 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X2) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X2)) := by
    intro sK1 X2 X0 sK0
    conv => enter [1]; rw [l30 sK1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l22 sK0 sK1 X2 sK1]
  have l32 : ∀ sK1 X2 X0 : G, ((sK1 ◇ sK1) ◇ X2) = (X0 ◇ ((sK1 ◇ sK1) ◇ X2)) := by
    intro sK1 X2 X0
    conv => enter [1]; rw [l31 sK1 X2 X0 sK1]
    conv => enter [1, 2, 1]; rw [← l28 sK1 sK1]
  have l33 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1 sK1]
    conv => enter [1]; rw [l23 sK1 sK1]
    conv => enter [1, 1]; rw [← l28 sK1 sK1]
  have l34 : ∀ X1 X2 sK1 X0 : G, (X1 ◇ X1) = (X2 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X1 X2 sK1 X0
    conv => enter [1]; rw [h41613 X1 X2 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l32 sK1 (X0 ◇ X1) X1]
  have l35 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l34 X1 X1 sK1 X0]
    conv => enter [1]; rw [← l21 sK0 sK1 (X0 ◇ X1) X1]
  have l36 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l35 X1 X1 sK1 X0]
    conv => enter [1, 1]; rw [← l28 sK1 X1]
  have l37 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l32 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l36 X0 sK1 (sK1 ◇ sK1)]
  have l38 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l37 sK1 X0]
    conv => enter [1]; rw [l36 X0 sK1 X1]
  have l39 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (((sK1 ◇ sK1) ◇ X0) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [← l37 sK1 X0]
  have l40 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l39 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l41 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l40 X0 X1 sK1]
    conv => enter [1]; rw [← l38 sK1 X1 X0]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1 sK1]
    conv => enter [1]; rw [← l33 sK1]
  intro x y z
  conv => enter [1]; rw [l42 x y]
  conv => enter [1]; rw [l28 y x]
  conv => enter [1]; rw [l20 x y z]

theorem Equation4512_41613_implies_Equation53959 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation53959 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l0 sK2 sK1 X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41613 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ X0)))]
  have l3 : ∀ sK2 sK1 X0 X1 X2 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK2 sK1 X0 X1 X2
    conv => enter [1]; rw [l1 sK2 sK1 (X0 ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41613 X0 (sK2 ◇ sK1) X1 X2]
  have l4 : ∀ X0 sK2 sK1 : G, (X0 ◇ X0) = ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h41613 X0 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0 X0]
    conv => enter [1]; rw [l3 sK2 sK1 X0 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41613 X0 X0 X0 X0]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l5 (sK2 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 sK1]
  have l8 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l5 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK2 sK1 (sK2 ◇ sK1)]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l8 sK2 sK1]
  have l10 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1) = (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1)) := by
    intro sK2 sK1 X1 X0
    conv => enter [1, 1]; rw [l6 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) X1]
  have l11 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [← l11 sK2 sK1]
  have l13 : ∀ X1 X2 sK2 sK1 X0 : G, (X1 ◇ X1) = (X2 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro X1 X2 sK2 sK1 X0
    conv => enter [1]; rw [h41613 X1 X2 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [← l10 sK2 sK1 (X0 ◇ X1) X1]
  have l14 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ X1) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [l13 X1 X1 sK2 sK1 X0]
    conv => enter [1]; rw [← l10 sK2 sK1 (X0 ◇ X1) X1]
  have l15 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (X0 ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l10 sK2 sK1 X0 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l14 X0 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l16 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [← l14 sK1 sK2 sK1 sK2]
  have l17 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l15 sK2 sK1 X0]
    conv => enter [1]; rw [l14 X0 sK2 sK1 X1]
  have l18 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) ◇ X1) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [← l15 sK2 sK1 X0]
  have l19 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l18 X0 X1 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0 X1]
  have l20 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l19 X0 X1 sK2 sK1]
    conv => enter [1]; rw [← l17 sK2 sK1 X1 X0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l12 sK1 sK0]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l16 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l22 x y z]

theorem Equation4512_41613_implies_Equation54270 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation54270 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK2 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h41613 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 sK1 sK2]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41613 (X1 ◇ X0) X2 X0 X1]
    conv => enter [1, 2]; rw [← h41613 X0 (X1 ◇ X0) X1 X1]
  have l7 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41613 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ X0)))]
  have l8 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ sK2) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ sK2)))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [h41613 sK2 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l4 sK0 sK1 sK2 (X0 ◇ (X1 ◇ sK2))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41613 X0 X0 X0 X0]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l6 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l11 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2))]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X0]
    conv => enter [1]; rw [l10 X0 X0 X1]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l8 sK2 sK0 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l14 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 (sK1 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l14 X0 sK2 sK1 sK1]
  have l16 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [← l15 X1 sK2 X1]
    conv => enter [1]; rw [l15 X1 sK2 X0]
  have l17 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l15 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l18 : ∀ X0 sK2 X1 X2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1 X2
    conv => enter [1]; rw [l16 X0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ sK2)]
  have l19 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1, 2]; rw [l16 sK1 sK2 X1]
    conv => enter [1]; rw [← l18 X0 sK2 X1 X1]
  have l20 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← l19 X1 sK1 sK2 sK1]
  have l21 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l16 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l22 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l20 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK2)) X1]
  have l23 : ∀ sK2 X2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X2) = (X0 ◇ ((sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) ◇ X2)) := by
    intro sK2 X2 X0 X1
    conv => enter [1, 1]; rw [h41613 sK2 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) X2]
  have l24 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h41613 sK2 (sK1 ◇ sK2) X0 sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l25 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l24 sK2 sK1 sK2]
    conv => enter [1]; rw [← l17 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l26 : ∀ sK2 X2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X2) = (X0 ◇ (sK2 ◇ ((X1 ◇ (sK2 ◇ sK2)) ◇ X2))) := by
    intro sK2 X2 X0 X1
    conv => enter [1]; rw [l23 sK2 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 (X1 ◇ (sK2 ◇ sK2)) X2]
  have l27 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l25 sK2 sK1]
    conv => enter [1]; rw [← l20 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l28 : ∀ sK2 X2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X2) = (X0 ◇ (sK2 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ X2)))) := by
    intro sK2 X2 X0 X1
    conv => enter [1]; rw [l26 sK2 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK2 ◇ sK2) X2]
  have l29 : ∀ sK2 X2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X2) = (X0 ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2))) := by
    intro sK2 X2 X0 sK1
    conv => enter [1]; rw [l28 sK2 X2 X0 sK2]
    conv => enter [1, 2, 2]; rw [← l21 sK1 sK2 X2 sK2]
  have l30 : ∀ sK2 X2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X2) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X2)) := by
    intro sK2 X2 X0 sK1
    conv => enter [1]; rw [l29 sK2 X2 X0 sK1]
    conv => enter [1, 2]; rw [← l22 sK1 sK2 X2 sK2]
  have l31 : ∀ sK2 X2 X0 : G, ((sK2 ◇ sK2) ◇ X2) = (X0 ◇ ((sK2 ◇ sK2) ◇ X2)) := by
    intro sK2 X2 X0
    conv => enter [1]; rw [l30 sK2 X2 X0 sK2]
    conv => enter [1, 2, 1]; rw [← l27 sK2 sK2]
  have l32 : ∀ sK2 X0 sK1 : G, (sK2 ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h41613 sK2 X0 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (sK1 ◇ sK2)]
  have l33 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l32 sK2 sK2 sK1]
    conv => enter [1]; rw [← l21 sK1 sK2 (sK1 ◇ sK2) sK2]
  have l34 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l33 sK2 sK1]
    conv => enter [1, 1]; rw [← l27 sK2 sK1]
  have l35 : ∀ X1 X2 sK2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro X1 X2 sK2 X0
    conv => enter [1]; rw [h41613 X1 X2 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l31 sK2 (X0 ◇ X1) X1]
  have l36 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ X1) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l35 X1 X1 sK2 X0]
    conv => enter [1]; rw [← l21 sK1 sK2 (X0 ◇ X1) X1]
  have l37 : ∀ X1 sK2 X0 : G, (X1 ◇ X1) = ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l36 X1 X1 sK2 X0]
    conv => enter [1, 1]; rw [← l27 sK2 X1]
  have l38 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l31 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l37 X0 sK2 (sK2 ◇ sK2)]
  have l39 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l38 sK2 X0]
    conv => enter [1]; rw [l37 X0 sK2 X1]
  have l40 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 1]; rw [l38 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l41 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l40 sK2 X0 X1]
  have l42 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l39 sK2 X1 X0]
    conv => enter [1]; rw [l41 sK2 X0 X1]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l42 sK2 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l34 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l27 y x]
  conv => enter [1]; rw [← l43 z x y]

theorem Equation4512_41613_implies_Equation54261 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41613 : Equation41613 G) : Equation54261 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41613 (sK0 ◇ (sK1 ◇ sK1)) X0 X1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41613 (sK1 ◇ sK1) X0 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [l6 sK1 sK0]
  have l9 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41613 (X1 ◇ X0) X2 X0 X1]
    conv => enter [1, 2]; rw [← h41613 X0 (X1 ◇ X0) X1 X1]
  have l10 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41613 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ X0)))]
  have l11 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41613 (sK0 ◇ sK1) (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l0 sK0 sK1 (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))]
  have l12 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41613 sK1 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ (X1 ◇ sK1))]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l11 sK0 sK1 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← h41613 X0 X0 X0 X0]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l9 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l16 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l8 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l4 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l17 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK1) (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1))]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X0]
    conv => enter [1]; rw [l15 X0 X0 X1]
  have l19 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41613 sK1 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l16 sK1 sK1 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l12 sK1 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l20 sK0 sK1 X0]
  have l22 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l18 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l21 sK1 sK1 X0]
  have l23 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [l22 sK1 X0]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41613 sK1 (sK1 ◇ (sK0 ◇ sK1)) X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (X0 ◇ (sK0 ◇ sK1)))]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l23 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l23 y x]
  conv => enter [1]; rw [← l26 z y]

@[equational_result]
theorem Equation41567_implies_Equation41565 (G : Type*) [Magma G] (h41567 : Equation41567 G) : Equation41565 G := by
  intro x y z
  conv => enter [1]; rw [h41567 x y z y]

@[equational_result]
theorem Equation41567_implies_Equation41566 (G : Type*) [Magma G] (h41567 : Equation41567 G) : Equation41566 G := by
  intro x y z
  conv => enter [1]; rw [h41567 x y z z]

theorem Equation4512_41567_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41567 : Equation41567 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X3 X0 X1 X2 X4
    conv => enter [1]; rw [h41567 X3 (X0 ◇ X1) X2 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41567 X0 X1 X2 X3]
  have l3 : ∀ sK1 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ X2))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41567 sK1 X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X1 ◇ (sK1 ◇ X2)))]
  have l4 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ X2))))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l2 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK1) sK1 sK1 sK1]
    conv => enter [1]; rw [← l4 sK1 sK1 sK1 sK1]
  have l7 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l5 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X3)) X4]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ X3) X4]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l9 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X3 X4]
  have l12 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41567 X0 X0 X0 (X0 ◇ X4)]
    conv => enter [1]; rw [← l11 X0 X4 X0 X0 X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l10 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1]; rw [← l12 (sK1 ◇ sK1) X0]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [← l14 sK1 X0]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41567 X0 (sK1 ◇ sK1) X0 X0]
    conv => enter [1, 2]; rw [← l15 sK1 (X0 ◇ (X0 ◇ X0))]
  intro x y
  conv => enter [1]; rw [l16 x y]

end Semigroup5
