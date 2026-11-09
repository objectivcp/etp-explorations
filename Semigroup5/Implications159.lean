import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation492_4512_implies_Equation14 (G : Type*) [Magma G] (h492 : Equation492 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h492 X0 X1 X0]
    conv => enter [1]; rw [← h492 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation14_4512_implies_Equation508 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation508 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK0 ◇ (sK2 ◇ sK2))]
  have l1 : ∀ sK2 : G, sK2 = ((sK2 ◇ sK2) ◇ sK2) := by
    intro sK2
    conv => enter [1]; rw [h14 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h14 sK2 sK2]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) sK1 X0]
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l1 sK2]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h14 (sK0 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1, 2]; rw [l3 sK0 sK2]
  have l5 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h14 sK0 sK2]
    conv => enter [1]; rw [← l4 sK0 sK2]
  have l6 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK0 ◇ (sK2 ◇ sK2))]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h14 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l6 sK1 sK0 sK2]
  have l8 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
    conv => enter [1]; rw [← l2 sK0 sK2 sK1 sK1]
  have l9 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l8 sK1 sK0 sK2]
    conv => enter [1, 1]; rw [← l5 sK0 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation508_4512_implies_Equation14 (G : Type*) [Magma G] (h508 : Equation508 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h508 (X0 ◇ (X2 ◇ X2)) X1 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h508 X0 (X0 ◇ (X2 ◇ X2)) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h508 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h508 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l2 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l5 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation14_4512_implies_Equation522 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation522 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h14 (sK2 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK2 ◇ (sK0 ◇ sK2))]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 sK0 sK1]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) sK1 X0]
  have l4 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation522_4512_implies_Equation14 (G : Type*) [Magma G] (h522 : Equation522 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h522 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h522 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation14_4512_implies_Equation543 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation543 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation543_4512_implies_Equation14 (G : Type*) [Magma G] (h543 : Equation543 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ sK0 sK1 X0 : G, sK0 = (sK1 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h543 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h543 X0 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X1 X0 : G, sK0 = (sK1 ◇ ((X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l1 sK0 sK1 (X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1)))]
    conv => enter [1, 2, 2]; rw [← h543 X0 (sK0 ◇ sK1) X1]
  have l3 : ∀ sK0 sK1 X1 X0 : G, sK0 = (sK1 ◇ (X1 ◇ ((X0 ◇ ((sK0 ◇ sK1) ◇ X1)) ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) X0]
  have l4 : ∀ sK0 sK1 X1 X0 : G, sK0 = (sK1 ◇ (X1 ◇ (X0 ◇ (((sK0 ◇ sK1) ◇ X1) ◇ X0)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 ((sK0 ◇ sK1) ◇ X1) X0]
  have l5 : ∀ sK0 sK1 X1 X0 : G, sK0 = (sK1 ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ X0))))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK0 ◇ sK1) X1 X0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h543 (sK0 ◇ sK1) sK0 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation14_4512_implies_Equation546 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation546 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h14 sK2 (sK0 ◇ (sK2 ◇ sK1))]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK0 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation546_4512_implies_Equation14 (G : Type*) [Magma G] (h546 : Equation546 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h546 X0 X0 X1]
    conv => enter [1]; rw [← h546 X1 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X0 X1 X1]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ X1) ◇ (X0 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h546 X2 (X1 ◇ X1) X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X1 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation14_4512_implies_Equation556 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation556 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK0 ◇ sK2)]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h14 (sK1 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h14 sK2 (sK1 ◇ (sK0 ◇ sK2))]
  have l2 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ sK2) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) sK1 X0]
  have l3 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK0 ◇ sK2)]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h14 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l3 sK1 sK0 sK2]
  have l5 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ sK1) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0 sK2]
    conv => enter [1]; rw [← l2 sK0 sK2 sK1 sK1]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← l5 sK1 sK0 sK2]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK2]
  have l8 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) sK2]
    conv => enter [1, 2]; rw [← l8 sK0 sK2 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 sK0 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation556_4512_implies_Equation14 (G : Type*) [Magma G] (h556 : Equation556 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h556 X1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h556 (X1 ◇ X0) X0 (X1 ◇ X0)]
  have l1 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h556 sK1 X0 (X0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h556 sK0 X0 sK1]
  have l2 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l1 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) sK0]
  have l3 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l2 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 (sK0 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h556 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK1 (sK0 ◇ sK1) sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation14_4512_implies_Equation572 (G : Type*) [Magma G] (h14 : Equation14 G) (h4512 : Equation4512 G) : Equation572 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h14 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h14 sK0 sK1]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h14 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h14 sK2 (sK0 ◇ sK1)]
  have l3 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l4 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) sK2 X0]
  have l5 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l1 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) sK1 X0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h14 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l3 sK1 sK0 sK0]
  have l9 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h14 sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  have l11 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← h14 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h14 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l11 sK1 sK2 sK0]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK0]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 sK1]
  have l14 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h14 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h14 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l14 sK2 sK0 sK1]
  have l16 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l15 sK2 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h14 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← l16 sK2 sK0 sK1]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
    conv => enter [1, 1]; rw [← l17 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l18 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation572_4512_implies_Equation14 (G : Type*) [Magma G] (h572 : Equation572 G) (h4512 : Equation4512 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h572 X0 X1 X1]
    conv => enter [1]; rw [← h572 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation16_implies_Equation466 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation466 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK1]
    conv => enter [1, 2]; rw [h16 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation466_4512_implies_Equation16 (G : Type*) [Magma G] (h466 : Equation466 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h466 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h466 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h466 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h466 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h466 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) X0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0 X0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h466 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2]; rw [← l11 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l11 sK1 sK0 sK0]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l20 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 (sK1 ◇ sK0)]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l22 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1, 2]; rw [l23 sK1 sK0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l24 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l27 x y]

theorem Equation16_4512_implies_Equation473 (G : Type*) [Magma G] (h16 : Equation16 G) (h4512 : Equation4512 G) : Equation473 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h16 X0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK1 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [l1 sK1 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h16 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h16 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h16 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h16 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation473_4512_implies_Equation16 (G : Type*) [Magma G] (h473 : Equation473 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h473 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [h473 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0))) sK1]
    conv => enter [1]; rw [← h473 X0 sK0]
  have l6 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 2]; rw [← l5 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ X0)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h473 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK1 ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [← l6 sK1 (sK1 ◇ sK0) sK0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation16_implies_Equation500 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation500 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK0]
    conv => enter [1]; rw [h16 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation500_4512_implies_Equation16 (G : Type*) [Magma G] (h500 : Equation500 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h500 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h500 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h500 X2 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h500 X1 X2]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X1 X0 X0]
    conv => enter [1]; rw [l2 X1 X1 X0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation16_implies_Equation528 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation528 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h16 sK0 sK2]
    conv => enter [1]; rw [h16 (sK2 ◇ (sK2 ◇ sK0)) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation528_4512_implies_Equation16 (G : Type*) [Magma G] (h528 : Equation528 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, sK0 = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h528 sK0 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l0 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← h528 (sK1 ◇ (sK1 ◇ sK0)) sK0 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation16_4512_implies_Equation562 (G : Type*) [Magma G] (h16 : Equation16 G) (h4512 : Equation4512 G) : Equation562 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (sK2 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [h16 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK0) X0]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [h16 (sK1 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK1 ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [← h16 X0 (sK2 ◇ sK0)]
  have l3 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK2 ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← h16 X0 sK0]
  have l4 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1, 2]; rw [h16 X0 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l1 sK1 sK2 sK0 ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)]
  have l5 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h16 ((sK2 ◇ sK0) ◇ X0) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 X0]
  have l6 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK1 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK2 sK0 X0]
  have l7 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l5 sK2 sK0 (sK2 ◇ sK0) sK1]
  have l8 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l7 sK2 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK2 ◇ sK0) sK2]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l4 sK2 (sK1 ◇ (sK2 ◇ sK0)) sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK2 sK1 sK0]
  have l10 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK1 sK0]
    conv => enter [1]; rw [l6 sK1 sK2 sK0 (sK2 ◇ sK0)]
  have l11 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h16 sK0 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h16 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation562_4512_implies_Equation16 (G : Type*) [Magma G] (h562 : Equation562 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h562 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h562 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h562 (sK1 ◇ (sK1 ◇ sK0)) sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation16_implies_Equation575 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation575 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h16 sK0 sK1]
    conv => enter [1, 2]; rw [h16 (sK1 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation575_4512_implies_Equation16 (G : Type*) [Magma G] (h575 : Equation575 G) (h4512 : Equation4512 G) : Equation16 G := by
  have l0 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X3 ◇ (X1 ◇ X0))) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [h575 (X3 ◇ (X3 ◇ (X1 ◇ X0))) X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h575 X0 X1 X3]
  have l1 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))) = (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1, 2, 2, 2]; rw [h575 (sK1 ◇ sK0) sK1 X1]
    conv => enter [1]; rw [← h575 (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1 X0]
  have l2 : ∀ sK0 X1 sK1 : G, sK0 = (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [h575 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK0 X1]
  have l3 : ∀ sK0 X0 X1 sK1 : G, sK0 = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l3 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l0 X0 X0 X2 X1]
    conv => enter [1]; rw [← h575 X2 X0 X0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation38_implies_Equation42 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation42 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation42_implies_Equation38 (G : Type*) [Magma G] (h42 : Equation42 G) : Equation38 G := by
  intro x y
  conv => enter [1]; rw [h42 x x y]

@[equational_result]
theorem Equation38_implies_Equation328 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation328 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation328_implies_Equation38 (G : Type*) [Magma G] (h328 : Equation328 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h328 X0 X1 X0]
    conv => enter [1]; rw [← h328 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation330 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation330 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation330_implies_Equation38 (G : Type*) [Magma G] (h330 : Equation330 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h330 X0 X1 X0]
    conv => enter [1]; rw [← h330 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation331 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation331 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation331_implies_Equation38 (G : Type*) [Magma G] (h331 : Equation331 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h331 X0 X1 X0 X0]
    conv => enter [1]; rw [← h331 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation322 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation322 G := by
  intro x y
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (x ◇ x)]

@[equational_result]
theorem Equation322_implies_Equation38 (G : Type*) [Magma G] (h322 : Equation322 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h322 X0 X1]
    conv => enter [1]; rw [← h322 X0 X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h322 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation38_implies_Equation324 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation324 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation324_implies_Equation38 (G : Type*) [Magma G] (h324 : Equation324 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h324 X0 X1 X0]
    conv => enter [1]; rw [← h324 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3325 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3325 G := by
  intro x y z
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (z ◇ (x ◇ x))]

@[equational_result]
theorem Equation3325_implies_Equation38 (G : Type*) [Magma G] (h3325 : Equation3325 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3325 X0 X1 X0]
    conv => enter [1]; rw [← h3325 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3327 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3327 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK0 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation3327_implies_Equation38 (G : Type*) [Magma G] (h3327 : Equation3327 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3327 X0 X1 X0]
    conv => enter [1]; rw [← h3327 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3328 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3328 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK1 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation3328_implies_Equation38 (G : Type*) [Magma G] (h3328 : Equation3328 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3328 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3328 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3329 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3329 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation3329_implies_Equation38 (G : Type*) [Magma G] (h3329 : Equation3329 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3329 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h3329 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3329 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h3329 sK0 X0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation38_implies_Equation3332 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3332 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK2 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation3332_implies_Equation38 (G : Type*) [Magma G] (h3332 : Equation3332 G) : Equation38 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3332 X2 X3 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h3332 X0 X1 X3 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3332 X0 X1 X0 X0]
    conv => enter [1]; rw [← l0 X0 X2 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x x y]

@[equational_result]
theorem Equation38_implies_Equation3333 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3333 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK2 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation3333_implies_Equation38 (G : Type*) [Magma G] (h3333 : Equation3333 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3333 X0 X1 X0]
    conv => enter [1]; rw [← h3333 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3335 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3335 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK2 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation3335_implies_Equation38 (G : Type*) [Magma G] (h3335 : Equation3335 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3335 X0 X1 X0]
    conv => enter [1]; rw [← h3335 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3336 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3336 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK3 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation3336_implies_Equation38 (G : Type*) [Magma G] (h3336 : Equation3336 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3336 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3336 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3337 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3337 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ sK1))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation3337_implies_Equation38 (G : Type*) [Magma G] (h3337 : Equation3337 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3337 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3337 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3339 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3339 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ sK3))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation3339_implies_Equation38 (G : Type*) [Magma G] (h3339 : Equation3339 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3339 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3339 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3340 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3340 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation3340_implies_Equation38 (G : Type*) [Magma G] (h3340 : Equation3340 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3340 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3340 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3341 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3341 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK1 ◇ sK0))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation3341_implies_Equation38 (G : Type*) [Magma G] (h3341 : Equation3341 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3341 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h3341 X0 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3305 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3305 G := by
  intro x y
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation3305_implies_Equation38 (G : Type*) [Magma G] (h3305 : Equation3305 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h3305 X0 X1]
    conv => enter [1]; rw [← h3305 X0 X2]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3307 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3307 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation3307_implies_Equation38 (G : Type*) [Magma G] (h3307 : Equation3307 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3307 X0 X1 X0]
    conv => enter [1]; rw [← h3307 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3311 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3311 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation3311_implies_Equation38 (G : Type*) [Magma G] (h3311 : Equation3311 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3311 X0 X1 X0]
    conv => enter [1]; rw [← h3311 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3313 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3313 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation3313_implies_Equation38 (G : Type*) [Magma G] (h3313 : Equation3313 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h3313 X0 X1 X0]
    conv => enter [1]; rw [← h3313 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation3310 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3310 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation3310_implies_Equation38 (G : Type*) [Magma G] (h3310 : Equation3310 G) : Equation38 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h3310 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h3310 X0 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h3310 X0 X1 X0]
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation3314 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation3314 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h38 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h38 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 x z w y]
  conv => enter [1]; rw [l0 x z w]

@[equational_result]
theorem Equation3314_implies_Equation38 (G : Type*) [Magma G] (h3314 : Equation3314 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h3314 X0 X1 X0 X0]
    conv => enter [1]; rw [← h3314 X0 X4 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation41806 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41806 G := by
  intro x y z
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (z ◇ (x ◇ (x ◇ x)))]

theorem Equation4512_41806_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41806 : Equation41806 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41806 X0 X1 X0]
    conv => enter [1]; rw [← h41806 X0 X2 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h41806 sK0 (sK0 ◇ X1) X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l1 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 X1 X0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h41806 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X1]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0]
  intro x y
  conv => enter [1]; rw [← l6 x y]

@[equational_result]
theorem Equation38_implies_Equation41808 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41808 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation41808_implies_Equation38 (G : Type*) [Magma G] (h41808 : Equation41808 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41808 X0 X1 X0]
    conv => enter [1]; rw [← h41808 X0 X2 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41809 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41809 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41809_implies_Equation38 (G : Type*) [Magma G] (h41809 : Equation41809 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41809 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41809 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41810 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41810 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41810_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41810 : Equation41810 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41810 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (X0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41810 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ (sK0 ◇ (X0 ◇ sK0)))]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (X0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 sK0 X0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41810 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41810 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h41810 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l7 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l8 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 X1]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l9 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41810 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l17 sK0 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l25 x y]

@[equational_result]
theorem Equation38_implies_Equation41812 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41812 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41812_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41812 : Equation41812 G) : Equation38 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ ((X3 ◇ (X0 ◇ (X1 ◇ X3))) ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h41812 X2 X0 (X3 ◇ (X0 ◇ (X1 ◇ X3)))]
    conv => enter [1, 2, 2, 2]; rw [← h41812 X0 X1 X3]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41812 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK1 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41812 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2, 2]; rw [l1 sK0 X0]
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41812 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41812 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ (X0 ◇ X1)))]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l10 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ X3)) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l2 X2 X0 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X3 (X0 ◇ (X1 ◇ X3)) (X2 ◇ (X0 ◇ X1))]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK1) sK0]
  have l13 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X3) ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l10 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X3) (X2 ◇ (X0 ◇ X1))]
  have l14 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1))))))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l13 X2 X0 X3 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X3 (X2 ◇ (X0 ◇ X1))]
  have l15 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ X2)) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l14 X2 X0 X3 X2]
    conv => enter [1, 2]; rw [← l5 X3 X2 X0 X2]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41812 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41812 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l16 X0 sK0]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1 X0]
    conv => enter [1]; rw [← l15 X0 X2 X0]
  have l19 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [← l15 sK0 (sK1 ◇ X1) X0]
    conv => enter [1]; rw [h4512 sK0 sK1 X1]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l21 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l20 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l19 sK0 sK0 sK1 X1]
  have l22 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 sK1 X1]
  have l23 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK1 X1]
  have l24 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 1]; rw [← l23 sK0 sK1 X0]
  have l25 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l23 sK0 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [l24 sK0 sK0 sK0 X1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l26 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l27 x y]

@[equational_result]
theorem Equation38_implies_Equation41813 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41813 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41813_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41813 : Equation41813 G) : Equation38 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41813 sK0 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41813 X2 X0 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h41813 X0 X1 X2 X2]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l0 sK0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 X1 ((sK0 ◇ sK0) ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation38_implies_Equation41814 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41814 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation41814_implies_Equation38 (G : Type*) [Magma G] (h41814 : Equation41814 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41814 X0 X1 X0]
    conv => enter [1]; rw [← h41814 X0 X2 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41816 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41816 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation41816_implies_Equation38 (G : Type*) [Magma G] (h41816 : Equation41816 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41816 X0 X1 X0]
    conv => enter [1]; rw [← h41816 X0 X2 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41817 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41817 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41817_implies_Equation38 (G : Type*) [Magma G] (h41817 : Equation41817 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41817 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41817 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41818 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41818 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41818_implies_Equation38 (G : Type*) [Magma G] (h41818 : Equation41818 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41818 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41818 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41820 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41820 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41820_implies_Equation38 (G : Type*) [Magma G] (h41820 : Equation41820 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41820 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41820 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41821 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41821 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41821_implies_Equation38 (G : Type*) [Magma G] (h41821 : Equation41821 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41821 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41821 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation41822 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41822 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation41822_implies_Equation38 (G : Type*) [Magma G] (h41822 : Equation41822 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41822 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41822 X0 X2 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41823 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41823 G := by
  intro x y z
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (z ◇ (y ◇ (x ◇ x)))]

theorem Equation4512_41823_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41823 : Equation41823 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h41823 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41823 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41823 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X0)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41823 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h41823 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 X0 sK0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1 X2]
    conv => enter [1]; rw [← l2 X2 X1 X2 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 sK0]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [l5 (sK0 ◇ sK0) sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l0 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation38_implies_Equation41825 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41825 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41825_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41825 : Equation41825 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = (sK0 ◇ ((sK1 ◇ X0) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h41825 sK0 X1 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41825 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = (sK0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l1 sK0 X1 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (X1 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41825 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l6 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l4 sK0 X1 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l7 : ∀ sK0 X1 sK1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l6 sK0 X1 sK1 sK0]
    conv => enter [1]; rw [← h41825 (sK0 ◇ sK1) X1 sK0]
  have l8 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h41825 X0 (sK0 ◇ sK1) X1]
    conv => enter [1, 2, 2]; rw [← l7 sK0 (X0 ◇ X1) sK1]
  have l9 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l8 X0 sK0 sK1 X0]
    conv => enter [1]; rw [← h41825 X0 sK0 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l11 x y]

@[equational_result]
theorem Equation38_implies_Equation41826 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41826 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41826_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41826 : Equation41826 G) : Equation38 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h41826 X2 X0 X3 (X1 ◇ (X0 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41826 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X1 X4 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X2 X0 X1 X4 X3
    conv => enter [1]; rw [h41826 X2 (X0 ◇ X1) X4 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X3 X2 X0 X1 X4 : G, (X3 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X3 X2 X0 X1 X4
    conv => enter [1]; rw [h41826 X3 X2 (X0 ◇ X1) X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l4 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ sK1) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h41826 X0 sK1 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 (X0 ◇ X1)]
  have l5 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41826 sK1 X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 sK1 (X1 ◇ (X0 ◇ (sK1 ◇ X2)))]
  have l6 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1 X2]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41826 X0 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1]; rw [← l4 X0 sK1 sK0 X0]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1 X2 X2]
    conv => enter [1]; rw [← l3 X2 X1 X2 X0 X2]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 X1 (sK0 ◇ sK1) (X0 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l9 sK0 sK0 X0 X1]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l7 sK0 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK1) X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l12 x y]

@[equational_result]
theorem Equation38_implies_Equation41827 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41827 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41827_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41827 : Equation41827 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41827 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41827 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ (X0 ◇ (X0 ◇ sK0)))]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 sK0 X0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41827 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41827 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41827 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1, 2, 2]; rw [← h41827 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l9 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41827 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 sK1]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))]
  have l19 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2, 2]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1 X0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK0 X0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK1)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l24 x y]

@[equational_result]
theorem Equation38_implies_Equation41829 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41829 G := by
  have l0 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h38 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l0 x z y y]

theorem Equation4512_41829_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41829 : Equation41829 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ ((X3 ◇ (X1 ◇ (X1 ◇ X3))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h41829 X2 X0 (X3 ◇ (X1 ◇ (X1 ◇ X3)))]
    conv => enter [1, 2, 2, 2]; rw [← h41829 X0 X1 X3]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41829 X2 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h41829 X0 X1 X0]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) (X0 ◇ X1)]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41829 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ ((X1 ◇ (X1 ◇ X3)) ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l1 X2 X0 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X3 (X1 ◇ (X1 ◇ X3)) (X0 ◇ (X0 ◇ X1))]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ X1)]
  have l7 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X1 ◇ ((X1 ◇ X3) ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l5 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X3) (X0 ◇ (X0 ◇ X1))]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1, 2]; rw [← h41829 X1 X0 X1]
  have l9 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1))))))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l7 X2 X0 X3 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X3 (X0 ◇ (X0 ◇ X1))]
  have l10 : ∀ X2 X0 X1 X3 : G, (X2 ◇ X0) = (X2 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l9 X2 X0 X3 X1]
    conv => enter [1]; rw [← l8 X2 (X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1))))) X3]
  have l11 : ∀ X2 X0 X1 X3 : G, (X2 ◇ X0) = (X2 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l10 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← l8 X1 (X3 ◇ (X0 ◇ (X0 ◇ X1))) X1]
  have l12 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [l11 X2 X0 X1 X3]
    conv => enter [1]; rw [← l8 X2 (X3 ◇ (X0 ◇ (X0 ◇ X1))) X1]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l12 X2 X0 X2 X1]
    conv => enter [1]; rw [← l8 X2 (X0 ◇ (X0 ◇ X1)) X2]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l13 X2 X0 X1]
    conv => enter [1, 2]; rw [← l8 X0 X1 X0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l8 (sK0 ◇ sK1) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l18 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l18 sK0 X0 sK1]
  have l20 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 sK1 (sK0 ◇ X0)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1]; rw [← l20 sK0 X0 sK1]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 sK0 X0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l23 sK0 sK1 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l27 x y]

@[equational_result]
theorem Equation38_implies_Equation41830 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41830 G := by
  have l0 : ∀ sK1 sK3 sK2 sK0 X0 : G, (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ X0) := by
    intro sK1 sK3 sK2 sK0 X0
    conv => enter [1]; rw [← h38 sK1 (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [h38 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [← l0 x z y w y]

theorem Equation4512_41830_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41830 : Equation41830 G) : Equation38 G := by
  have l0 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [h41830 X1 sK0 X2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41830 X2 X1 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h41830 X0 X1 X1 X2]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l0 X1 sK0 X1 X0]
    conv => enter [1]; rw [← l1 X1 ((sK0 ◇ sK0) ◇ X0) X1]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ X0) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l2 X1 sK0 X0]
    conv => enter [1]; rw [← l1 X1 X0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x x y]

@[equational_result]
theorem Equation38_implies_Equation41831 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41831 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41831_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41831 : Equation41831 G) : Equation38 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41831 X0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41831 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41831 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1, 2]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41831 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l14 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l16 X0 sK0]
    conv => enter [1]; rw [← l2 X0 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK1)]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [l17 X0 sK0]
  have l20 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l17 X0 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l17 (sK0 ◇ sK1) sK0]
  have l22 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l20 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41831 (sK0 ◇ sK1) sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l22 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK1) ◇ sK0)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41831 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l21 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK0 ((sK0 ◇ sK1) ◇ sK0)]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ sK0)]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1, 2]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1, 2]; rw [← l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1, 2]; rw [l33 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l35 x y]

@[equational_result]
theorem Equation38_implies_Equation41834 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41834 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41834_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41834 : Equation41834 G) : Equation38 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [h41834 X4 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41834 X1 X2 X0 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [← h41834 X0 X0 X2 X1]
  have l4 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [h41834 X4 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
  have l5 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [l4 X4 X2 X0 X1 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l6 : ∀ X4 X2 X1 : G, (X4 ◇ X2) = (X4 ◇ (X1 ◇ X2)) := by
    intro X4 X2 X1
    conv => enter [1]; rw [l5 X4 X2 X4 X1 X4]
    conv => enter [1]; rw [← l2 X4 X1 X2 X4 (X1 ◇ X4)]
  have l7 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l7 sK0 X0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l11 x y]

@[equational_result]
theorem Equation38_implies_Equation41835 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41835 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41835_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41835 : Equation41835 G) : Equation38 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X0) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h41835 (X1 ◇ (X2 ◇ X0)) X0 X3 X1]
    conv => enter [1, 2, 2]; rw [← h41835 X0 X1 X1 X2]
  have l1 : ∀ X3 X0 X1 X4 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X0 X1 X4 X2
    conv => enter [1]; rw [h41835 X3 (X0 ◇ X1) X4 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [h41835 X4 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X1) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l1 X3 X0 X1 X3 X3]
    conv => enter [1]; rw [← l2 X3 X1 X3 X0 X3]
  have l4 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X0) = (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X3 ◇ (X0 ◇ X1))]
  have l5 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ X0) = (X1 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l4 X1 X2 X0 X3]
    conv => enter [1]; rw [← h41835 X1 X3 (X2 ◇ X0) X0]
  have l6 : ∀ X1 X3 X2 X0 : G, (X1 ◇ X3) = (X1 ◇ ((X2 ◇ X0) ◇ X0)) := by
    intro X1 X3 X2 X0
    conv => enter [1]; rw [← l5 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) X0]
  have l7 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X1 ◇ X0) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l6 X1 X3 X1 X0]
    conv => enter [1]; rw [l3 X1 (X1 ◇ X0) X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

@[equational_result]
theorem Equation38_implies_Equation41837 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41837 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41837_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41837 : Equation41837 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (X1 ◇ ((sK0 ◇ X0) ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h41837 X1 X2 (sK0 ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X3 X1 X0 X2 : G, (X3 ◇ X1) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [h41837 X3 X1 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h41837 (X0 ◇ X1) X2 X1 X0]
  have l3 : ∀ X3 X1 X0 X2 : G, (X3 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [l2 X3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (X1 ◇ (sK0 ◇ (X0 ◇ (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l1 X1 X2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X2 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X1 ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l4 X1 X2 X1 X0]
    conv => enter [1]; rw [← l3 X1 X0 X1 (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0)))]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l6 x y]

@[equational_result]
theorem Equation38_implies_Equation41838 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41838 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41838_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41838 : Equation41838 G) : Equation38 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l2 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h41838 X2 X0 X3 (X1 ◇ (X2 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41838 X0 X1 (X1 ◇ (X2 ◇ X2)) X2]
  have l3 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [h41838 X4 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l4 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ sK1) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X0)))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [h41838 X1 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 (X0 ◇ X0)]
  have l5 : ∀ X1 sK1 sK0 : G, (X1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [l4 X1 sK1 sK0 X1]
    conv => enter [1]; rw [← h41838 X1 (sK0 ◇ sK1) sK0 X1]
  have l6 : ∀ X4 X2 X0 : G, (X4 ◇ X2) = (X4 ◇ (X0 ◇ X2)) := by
    intro X4 X2 X0
    conv => enter [1]; rw [l3 X4 X2 X0 X4 X4]
    conv => enter [1, 2]; rw [← h41838 X0 X2 X4 X4]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l6 (sK0 ◇ sK1) X0 X1]
  have l8 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l2 sK0 X1 (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 X0 X1]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1]; rw [← l10 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x x y]

@[equational_result]
theorem Equation38_implies_Equation41839 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41839 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

theorem Equation4512_41839_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41839 : Equation41839 G) : Equation38 G := by
  have l0 : ∀ X5 X2 X0 X1 X3 X4 : G, (X5 ◇ X2) = (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X5 X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41839 X5 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l1 : ∀ X5 X2 X1 : G, (X5 ◇ X2) = (X5 ◇ X1) := by
    intro X5 X2 X1
    conv => enter [1]; rw [l0 X5 X2 X5 X1 X5 X5]
    conv => enter [1]; rw [← h41839 X5 X1 X5 X2 (X5 ◇ X5)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation38_implies_Equation41840 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41840 G := by
  intro x y z
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (z ◇ (z ◇ (x ◇ x)))]

theorem Equation4512_41840_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41840 : Equation41840 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41840 X0 X1 X0]
    conv => enter [1]; rw [← h41840 X0 X2 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h41840 sK0 (sK0 ◇ X1) X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h41840 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 X1]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation38_implies_Equation41842 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41842 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation41842_implies_Equation38 (G : Type*) [Magma G] (h41842 : Equation41842 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41842 X0 X1 X0]
    conv => enter [1]; rw [← h41842 X0 X2 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41843 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41843 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41843_implies_Equation38 (G : Type*) [Magma G] (h41843 : Equation41843 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41843 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41843 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41844 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41844 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41844_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41844 : Equation41844 G) : Equation38 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h41844 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ sK0) = ((sK0 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41844 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41844 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1))))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ sK0) = (sK0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← l0 X1 X2 X0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← h41844 X0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 X0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41844 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41844 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41844 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h41844 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) X0 X0]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [h41844 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) X0 X0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l11 sK0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41844 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l17 sK0 X0]
  have l20 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l20 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l22 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l19 X0 sK0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l23 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l22 X0 sK0]
    conv => enter [1, 2]; rw [← l18 sK0]
  have l24 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41844 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l23 X0 sK0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0 sK0]
    conv => enter [1]; rw [← l21 sK0 (X0 ◇ X0) sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [← l26 sK0 X0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41844 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l27 sK0 ((sK0 ◇ sK0) ◇ (X1 ◇ X0))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [← l28 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l29 x y]

@[equational_result]
theorem Equation38_implies_Equation41847 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41847 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK3 ◇ (sK2 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41847_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41847 : Equation41847 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41847 X2 X3 X0 (X3 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41847 X0 X1 X3 X2]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41847 X2 X0 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h41847 X0 X1 X0 X2]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41847 (sK0 ◇ sK0) X0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X0 ◇ X1))]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l5 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X2 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l1 X2 X0 X3 X2]
    conv => enter [1]; rw [← l2 X2 X3 (X3 ◇ X2)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← l4 sK0 X0 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

@[equational_result]
theorem Equation38_implies_Equation41848 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41848 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation41848_implies_Equation38 (G : Type*) [Magma G] (h41848 : Equation41848 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41848 X0 X1 X0]
    conv => enter [1]; rw [← h41848 X0 X2 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41850 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41850 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation41850_implies_Equation38 (G : Type*) [Magma G] (h41850 : Equation41850 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41850 X0 X1 X0]
    conv => enter [1]; rw [← h41850 X0 X2 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41851 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41851 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41851_implies_Equation38 (G : Type*) [Magma G] (h41851 : Equation41851 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41851 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41851 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41852 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41852 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41852_implies_Equation38 (G : Type*) [Magma G] (h41852 : Equation41852 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41852 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41852 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41854 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41854 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41854_implies_Equation38 (G : Type*) [Magma G] (h41854 : Equation41854 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41854 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41854 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41855 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41855 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41855_implies_Equation38 (G : Type*) [Magma G] (h41855 : Equation41855 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41855 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41855 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation41856 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41856 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation41856_implies_Equation38 (G : Type*) [Magma G] (h41856 : Equation41856 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41856 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41856 X0 X2 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41857 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41857 G := by
  intro x y z w
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (z ◇ (w ◇ (x ◇ x)))]

theorem Equation4512_41857_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41857 : Equation41857 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41857 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41857 X0 X2 X0 X0]
  have l1 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h41857 sK0 (sK0 ◇ X2) X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l2 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [h41857 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 X2]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation38_implies_Equation41859 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41859 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41859_implies_Equation38 (G : Type*) [Magma G] (h41859 : Equation41859 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41859 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41859 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41860 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41860 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41860_implies_Equation38 (G : Type*) [Magma G] (h41860 : Equation41860 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41860 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41860 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41861 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41861 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation41861_implies_Equation38 (G : Type*) [Magma G] (h41861 : Equation41861 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41861 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41861 X0 X2 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41862 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41862 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41862_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41862 : Equation41862 G) : Equation38 G := by
  have l0 : ∀ X2 X3 X1 X0 X4 X5 : G, ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X0) = ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ (X4 ◇ (X5 ◇ (X0 ◇ X1)))) := by
    intro X2 X3 X1 X0 X4 X5
    conv => enter [1]; rw [h41862 (X2 ◇ (X3 ◇ (X1 ◇ X0))) X0 X4 X5]
    conv => enter [1, 2, 2, 2]; rw [← h41862 X0 X1 X2 X3]
  have l1 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1]; rw [h41862 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [h41862 X4 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l2 X2 X1 X2 X2 X0]
    conv => enter [1]; rw [← l1 X2 X0 X1 X2 X2]
  have l4 : ∀ X2 X3 X1 X0 X4 X5 : G, ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X0) = (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ (X4 ◇ (X5 ◇ (X0 ◇ X1))))) := by
    intro X2 X3 X1 X0 X4 X5
    conv => enter [1]; rw [l0 X2 X3 X1 X0 X4 X5]
    conv => enter [1]; rw [← h4512 X2 (X3 ◇ (X1 ◇ X0)) (X4 ◇ (X5 ◇ (X0 ◇ X1)))]
  have l5 : ∀ X2 X3 X1 X0 X4 X5 : G, ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X0) = (X2 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X1)))) := by
    intro X2 X3 X1 X0 X4 X5
    conv => enter [1]; rw [l4 X2 X3 X1 X0 X4 X5]
    conv => enter [1]; rw [← l3 X2 (X4 ◇ (X5 ◇ (X0 ◇ X1))) (X3 ◇ (X1 ◇ X0))]
  have l6 : ∀ X2 X3 X1 X0 X5 : G, ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X0) = (X2 ◇ (X5 ◇ (X0 ◇ X1))) := by
    intro X2 X3 X1 X0 X5
    conv => enter [1]; rw [l5 X2 X3 X1 X0 X2 X5]
    conv => enter [1]; rw [← l3 X2 (X5 ◇ (X0 ◇ X1)) X2]
  have l7 : ∀ X2 X3 X1 X0 : G, ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X1 X0
    conv => enter [1]; rw [l6 X2 X3 X1 X0 X2]
    conv => enter [1]; rw [← l3 X2 (X0 ◇ X1) X2]
  have l8 : ∀ X2 X1 X3 X0 : G, (X2 ◇ X1) = ((X2 ◇ (X3 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l3 X2 X1 X0]
    conv => enter [1]; rw [← l7 X2 X3 X1 X0]
  have l9 : ∀ X2 X1 X3 X0 : G, (X2 ◇ X1) = (X2 ◇ ((X3 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l8 X2 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X2 (X3 ◇ (X1 ◇ X0)) X0]
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ X0) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l9 X2 X1 X2 X0]
    conv => enter [1]; rw [← l3 X2 X0 (X2 ◇ (X1 ◇ X0))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l11 x y]

@[equational_result]
theorem Equation38_implies_Equation41864 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41864 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41864_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41864 : Equation41864 G) : Equation38 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X0 X1 X2 X4
    conv => enter [1]; rw [h41864 X3 (X0 ◇ X1) X2 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X1 sK0 sK1 X0 X2 : G, (X1 ◇ sK0) = (X1 ◇ ((sK1 ◇ X0) ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro X1 sK0 sK1 X0 X2
    conv => enter [1]; rw [h41864 X1 sK0 (sK1 ◇ X0) X2]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l3 : ∀ X4 X2 X3 X0 X1 : G, (X4 ◇ X2) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X2 X3 X0 X1
    conv => enter [1]; rw [h41864 X4 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l4 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ sK1) = (X1 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [h41864 X1 sK1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK1 X0]
  have l5 : ∀ X1 sK0 sK1 : G, (X1 ◇ (sK0 ◇ sK1)) = (X1 ◇ sK1) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [h41864 X1 (sK0 ◇ sK1) X1 sK0]
    conv => enter [1]; rw [← l4 X1 sK1 X1 sK0]
  have l6 : ∀ X1 sK0 sK1 X0 X2 : G, (X1 ◇ sK0) = (X1 ◇ (sK1 ◇ (X0 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro X1 sK0 sK1 X0 X2
    conv => enter [1]; rw [l2 X1 sK0 sK1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (X2 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l7 : ∀ X3 X1 X0 : G, (X3 ◇ X1) = (X3 ◇ (X0 ◇ X1)) := by
    intro X3 X1 X0
    conv => enter [1]; rw [l3 X3 X1 X3 X3 X0]
    conv => enter [1]; rw [← l1 X3 X0 X1 X3 X3]
  have l8 : ∀ X1 sK0 sK1 : G, (X1 ◇ sK0) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [l6 X1 sK0 sK1 X1 X1]
    conv => enter [1, 2]; rw [← h41864 sK1 (sK0 ◇ sK1) X1 X1]
  have l9 : ∀ X1 sK0 sK1 : G, (X1 ◇ (sK0 ◇ sK1)) = (X1 ◇ sK0) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [l7 X1 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l8 X1 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation38_implies_Equation41865 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41865 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4512_41865_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41865 : Equation41865 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41865 X2 X3 X0 (X1 ◇ X3)]
    conv => enter [1, 2]; rw [← h41865 X0 X1 (X1 ◇ X3) X3]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41865 (sK0 ◇ sK0) X0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41865 sK0 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l2 sK0 X0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41865 X0 X1 X0 X0]
    conv => enter [1]; rw [← l1 X0 X2 X0 (X0 ◇ (X1 ◇ X0))]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK1) X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

@[equational_result]
theorem Equation38_implies_Equation41866 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41866 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

theorem Equation4512_41866_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41866 : Equation41866 G) : Equation38 G := by
  have l0 : ∀ X5 X3 X0 X1 X2 X4 : G, (X5 ◇ X3) = (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X5 X3 X0 X1 X2 X4
    conv => enter [1]; rw [h41866 X5 X3 (X0 ◇ X1) X2 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l1 : ∀ X5 X3 X2 : G, (X5 ◇ X3) = (X5 ◇ X2) := by
    intro X5 X3 X2
    conv => enter [1]; rw [l0 X5 X3 X5 X5 X2 X5]
    conv => enter [1]; rw [← h41866 X5 X2 X5 X5 (X3 ◇ X5)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation38_implies_Equation41867 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41867 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41867_implies_Equation38 (G : Type*) [Magma G] (h41867 : Equation41867 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41867 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41867 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41869 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41869 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41869_implies_Equation38 (G : Type*) [Magma G] (h41869 : Equation41869 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41869 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41869 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41870 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41870 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41870_implies_Equation38 (G : Type*) [Magma G] (h41870 : Equation41870 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41870 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41870 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41871 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41871 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK4 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK1 ◇ (sK4 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation41871_implies_Equation38 (G : Type*) [Magma G] (h41871 : Equation41871 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41871 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41871 X0 X2 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41872 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41872 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41872_implies_Equation38 (G : Type*) [Magma G] (h41872 : Equation41872 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41872 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41872 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41874 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41874 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41874_implies_Equation38 (G : Type*) [Magma G] (h41874 : Equation41874 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41874 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41874 X0 X2 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41875 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41875 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation41875_implies_Equation38 (G : Type*) [Magma G] (h41875 : Equation41875 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41875 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41875 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation41876 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41876 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation41876_implies_Equation38 (G : Type*) [Magma G] (h41876 : Equation41876 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41876 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41876 X0 X2 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41877 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41877 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation41877_implies_Equation38 (G : Type*) [Magma G] (h41877 : Equation41877 G) : Equation38 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h41877 X0 X2 X0 X0 X0]
    conv => enter [1]; rw [← h41877 X0 X1 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41879 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41879 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK4)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation41879_implies_Equation38 (G : Type*) [Magma G] (h41879 : Equation41879 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41879 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41879 X0 X2 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41880 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41880 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation41880_implies_Equation38 (G : Type*) [Magma G] (h41880 : Equation41880 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41880 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41880 X0 X2 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41881 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41881 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 sK3]
    conv => enter [1]; rw [h38 sK2 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

@[equational_result]
theorem Equation41881_implies_Equation38 (G : Type*) [Magma G] (h41881 : Equation41881 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41881 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41881 X0 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation38_implies_Equation41882 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41882 G := by
  have l0 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h38 sK3 sK4]
    conv => enter [1]; rw [h38 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y z w u v]

@[equational_result]
theorem Equation41882_implies_Equation38 (G : Type*) [Magma G] (h41882 : Equation41882 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41882 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h41882 X0 X2 X0 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41732 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41732 G := by
  intro x y
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (x ◇ (x ◇ (x ◇ x)))]

theorem Equation4512_41732_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41732 : Equation41732 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41732 X0 X1]
    conv => enter [1]; rw [← h41732 X0 X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [h41732 sK0 (sK1 ◇ X0)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41732 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 1]; rw [← l11 sK0 sK1 X0]
  have l13 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [l12 sK0 sK0 sK0 X1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation38_implies_Equation41734 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41734 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation41734_implies_Equation38 (G : Type*) [Magma G] (h41734 : Equation41734 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41734 X0 X1 X0]
    conv => enter [1]; rw [← h41734 X0 X3 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41738 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41738 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation41738_implies_Equation38 (G : Type*) [Magma G] (h41738 : Equation41738 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41738 X0 X1 X0]
    conv => enter [1]; rw [← h41738 X0 X3 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41740 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41740 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation41740_implies_Equation38 (G : Type*) [Magma G] (h41740 : Equation41740 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41737 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41737 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41737_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation38 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41737 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ sK1) ◇ sK0)]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation38_implies_Equation41741 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41741 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h38 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h38 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 x z w y]
  conv => enter [1]; rw [l0 x z w]

@[equational_result]
theorem Equation41741_implies_Equation38 (G : Type*) [Magma G] (h41741 : Equation41741 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41752 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41752 G := by
  intro x y z
  conv => enter [1]; rw [← h38 x y]
  conv => enter [1]; rw [h38 x (x ◇ (z ◇ (x ◇ x)))]

theorem Equation4512_41752_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41752 : Equation41752 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41752 X0 X1 X0]
    conv => enter [1]; rw [← h41752 X0 X3 X0]
  have l1 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [← h41752 sK0 (sK1 ◇ X1) X0]
    conv => enter [1]; rw [h4512 sK0 sK1 X1]
  have l2 : ∀ sK0 X0 sK1 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l1 sK0 X0 sK1 X1]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41752 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 sK1 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK1 X1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 1]; rw [← l4 sK0 sK1 X0]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [l5 sK0 sK0 sK0 X1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation38_implies_Equation41754 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41754 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation41754_implies_Equation38 (G : Type*) [Magma G] (h41754 : Equation41754 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41754 X0 X1 X0]
    conv => enter [1]; rw [← h41754 X0 X3 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41744 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41744 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41744_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41744 : Equation41744 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41744 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41744 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
    conv => enter [1]; rw [← h41744 (sK0 ◇ sK0) X0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l2 sK0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation38_implies_Equation41755 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41755 G := by
  have l0 : ∀ sK1 sK3 sK2 : G, (sK1 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))) := by
    intro sK1 sK3 sK2
    conv => enter [1]; rw [← h38 sK1 sK3]
    conv => enter [1]; rw [h38 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3)))]
  have l1 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK3) = (sK1 ◇ sK0) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 sK3]
    conv => enter [1]; rw [h38 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y w]
  conv => enter [1]; rw [l0 x w z]

@[equational_result]
theorem Equation41755_implies_Equation38 (G : Type*) [Magma G] (h41755 : Equation41755 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41755 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41755 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41760 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41760 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation41760_implies_Equation38 (G : Type*) [Magma G] (h41760 : Equation41760 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41760 X0 X1 X0]
    conv => enter [1]; rw [← h41760 X0 X3 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41762 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41762 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]
  conv => enter [1]; rw [l0 x z]

@[equational_result]
theorem Equation41762_implies_Equation38 (G : Type*) [Magma G] (h41762 : Equation41762 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41762 X0 X1 X0]
    conv => enter [1]; rw [← h41762 X0 X3 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41747 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41747 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41747_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation38 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41747 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l1 X3 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ X0) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l2 X3 X0 X1 X3]
    conv => enter [1]; rw [← l0 X3 X0 (X1 ◇ (X0 ◇ (X1 ◇ X3)))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h41747 X0 X1 X0]
    conv => enter [1]; rw [l3 X0 X0 (X1 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation38_implies_Equation41763 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41763 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [h38 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [h38 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 x z w y]
  conv => enter [1]; rw [l0 x z w]

@[equational_result]
theorem Equation41763_implies_Equation38 (G : Type*) [Magma G] (h41763 : Equation41763 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41763 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41763 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41748 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41748 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_41748_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41748 : Equation41748 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41748 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41748 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ sK0))]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [← h41748 X0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41748 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [l3 X0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l7 : ∀ X0 sK0 X1 : G, ((X0 ◇ sK0) ◇ X1) = ((X0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41748 (X0 ◇ sK0) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 X0]
  have l8 : ∀ X0 sK0 X1 : G, ((X0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ ((X0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l7 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 ((X0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0)))]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1]; rw [← l6 sK0 X0 X1]
  have l11 : ∀ X0 sK0 X1 : G, ((X0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ X0)))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l8 X0 sK0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l12 : ∀ X0 sK0 X1 : G, ((X0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l11 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l10 sK0 X0 (sK0 ◇ (X1 ◇ (sK0 ◇ X0)))]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 sK0 X1]
    conv => enter [1]; rw [l12 X0 sK0 X1]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41748 sK0 X0 sK0]
    conv => enter [1]; rw [l13 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l15 sK0 X0]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation38_implies_Equation41756 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41756 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]
  conv => enter [1]; rw [l0 x z y]

theorem Equation4512_41756_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41756 : Equation41756 G) : Equation38 G := by
  have l0 : ∀ X0 X2 X1 X3 : G, ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1)))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [h41756 (X0 ◇ (X2 ◇ (X1 ◇ X0))) X0 X3]
    conv => enter [1, 2, 2, 2]; rw [← h41756 X0 X1 X2]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h41756 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41756 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1 X2]
    conv => enter [1]; rw [← l2 X2 X1 X2 X0]
  have l4 : ∀ X0 X2 X1 X3 : G, ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1))))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l0 X0 X2 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ (X1 ◇ X0)) ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1)))]
  have l5 : ∀ X0 X2 X1 X3 : G, ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = (X0 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1)))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l4 X0 X2 X1 X3]
    conv => enter [1]; rw [l3 X0 (X2 ◇ (X1 ◇ X0)) ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X3 ◇ (X0 ◇ X1)))]
  have l6 : ∀ X0 X2 X1 X3 : G, ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = (X0 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l5 X0 X2 X1 X3]
    conv => enter [1]; rw [l3 X0 (X0 ◇ (X2 ◇ (X1 ◇ X0))) (X3 ◇ (X0 ◇ X1))]
  have l7 : ∀ X0 X2 X1 : G, ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1 X0]
    conv => enter [1, 2]; rw [l3 X0 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ (X2 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X0 X0 X1]
    conv => enter [1]; rw [← l7 X0 X2 X1]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ (X1 ◇ X0)) X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1 X0]
    conv => enter [1]; rw [l3 X0 (X0 ◇ (X1 ◇ X0)) X0]
  intro x y
  conv => enter [1]; rw [← l10 x y]

@[equational_result]
theorem Equation38_implies_Equation41764 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41764 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK3 ◇ sK1))]
    conv => enter [1]; rw [h38 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK1))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK3 ◇ sK1))]
    conv => enter [1]; rw [h38 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 x z w y]
  conv => enter [1]; rw [l0 x z w]

@[equational_result]
theorem Equation41764_implies_Equation38 (G : Type*) [Magma G] (h41764 : Equation41764 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41764 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41764 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41758 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41758 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h38 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]
  conv => enter [1]; rw [l0 x z y]

theorem Equation4512_41758_implies_Equation38 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41758 : Equation41758 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41758 X1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41758 X2 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h41758 (X0 ◇ (X1 ◇ X0)) X1 X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41758 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (X0 ◇ X1))]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41758 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X1 ◇ (X0 ◇ X1))]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X1]
  have l7 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l1 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1)))]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X1]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41758 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41758 sK0 X0 X1]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2, 2, 2]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h41758 X1 (sK0 ◇ sK0) (sK0 ◇ X0)]
  have l15 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l14 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [l0 sK0 (X1 ◇ (X0 ◇ X1))]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l19 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [l7 X1 sK0 X1]
    conv => enter [1]; rw [← l15 X1 sK0 X1]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1]; rw [← l13 sK0 (X1 ◇ (X0 ◇ X1))]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
    conv => enter [1]; rw [← l20 sK0 X0 sK0]
  have l23 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l19 X0 sK0]
  have l24 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l23 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l25 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41758 X1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK0 X0]
  have l26 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l25 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ X0)]
  have l27 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l26 X1 sK0 X0]
    conv => enter [1]; rw [← l9 X1 (sK0 ◇ sK0) X0]
  have l28 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l27 X1 sK0 X0]
    conv => enter [1]; rw [l24 X1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l28 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l19 X0 sK0]
  have l30 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l21 sK0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h41758 (sK0 ◇ sK0) X1 X0]
  have l31 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 X1 sK0]
    conv => enter [1]; rw [l30 sK0 sK0 X1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41758 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← l22 sK0 (X0 ◇ sK0)]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l29 (sK0 ◇ sK0) sK0 X0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 sK0]
    conv => enter [1]; rw [← l35 sK0 X0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l38 x y]

@[equational_result]
theorem Equation38_implies_Equation41766 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41766 G := by
  have l0 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK3 ◇ sK2))]
    conv => enter [1]; rw [h38 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h38 sK1 (sK2 ◇ (sK3 ◇ sK2))]
    conv => enter [1]; rw [h38 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 x z w y]
  conv => enter [1]; rw [l0 x z w]

@[equational_result]
theorem Equation41766_implies_Equation38 (G : Type*) [Magma G] (h41766 : Equation41766 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41766 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41766 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation38_implies_Equation41750 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41750 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

end Semigroup5
