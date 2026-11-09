import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41791_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41791 : Equation41791 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41791 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ X0))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41791 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ (sK0 ◇ X0))]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41791 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (sK1 ◇ X0))]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ X0) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 ((sK1 ◇ sK2) ◇ X0)]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
    conv => enter [1]; rw [← h41791 (sK1 ◇ sK2) sK2 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ (sK1 ◇ sK2))]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)]
    conv => enter [1]; rw [← h41791 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l17 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l16 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 (sK0 ◇ X0)]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK0 ◇ sK2)]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2 sK2]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

@[equational_result]
theorem Equation327_implies_Equation41792 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41792 G := by
  intro x y z w
  conv => enter [1]; rw [h327 x y (z ◇ (x ◇ w))]

theorem Equation4512_41792_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41792 : Equation41792 G) : Equation327 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h41792 X0 X1 X2 X2]
    conv => enter [1]; rw [← h41792 X2 X0 X1 (X0 ◇ X2)]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41792 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ X1))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l3 x y z]

@[equational_result]
theorem Equation327_implies_Equation41793 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41793 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (z ◇ (y ◇ x))]

theorem Equation4512_41793_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41793 : Equation41793 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41793 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41793 (sK1 ◇ sK0) X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l3 sK1 sK0 X0]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41793 sK1 sK0 X0]
    conv => enter [1]; rw [l5 sK1 sK0 X0]
  have l7 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK0) X0]
  have l8 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l7 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
  have l9 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l8 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l6 sK1 sK0 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 X0 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation327_implies_Equation41795 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41795 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (z ◇ (y ◇ z))]

theorem Equation4512_41795_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41795 : Equation41795 G) : Equation327 G := by
  have l0 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK2 ◇ X0) ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h41795 X1 sK1 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ sK1) = (X1 ◇ (sK1 ◇ (sK2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l0 X1 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 X0 ((sK1 ◇ sK2) ◇ X0)]
  have l2 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ sK1) = (X1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l1 X1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (X0 ◇ ((sK1 ◇ sK2) ◇ X0))]
  have l3 : ∀ X1 sK1 sK2 : G, (X1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [l2 X1 sK1 sK2 X1]
    conv => enter [1]; rw [← h41795 X1 (sK1 ◇ sK2) X1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation327_implies_Equation41796 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41796 G := by
  intro x y z w
  conv => enter [1]; rw [h327 x y (z ◇ (y ◇ w))]

theorem Equation4512_41796_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41796 : Equation41796 G) : Equation327 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41796 X2 X0 X1 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h41796 X0 X1 X0 X2]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41796 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK1 ◇ X1))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) X0 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l3 x y z]

@[equational_result]
theorem Equation327_implies_Equation41797 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41797 G := by
  intro x y z
  conv => enter [1]; rw [h327 x y (z ◇ (z ◇ x))]

theorem Equation4512_41797_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41797 : Equation41797 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h41797 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [← h41797 X0 X1 X1]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41797 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3)) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X2 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← h41797 X0 X1 X2]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41797 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X0 ◇ sK0))]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X3)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ X1)]
  have l7 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l5 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X0)) X3]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l7 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X2 ◇ X0) X3]
  have l10 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l9 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 X3]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h41797 sK2 X0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK2) sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2]
  have l16 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X0)) = ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l8 (X1 ◇ (X2 ◇ (X2 ◇ X0))) X0]
    conv => enter [1, 2, 2]; rw [← h41797 X0 X1 X2]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l15 sK0 sK1 sK2]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h41797 X0 X0 X1]
    conv => enter [1, 2]; rw [l8 X0 X1]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l8 (X0 ◇ X1) X2]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
  have l22 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l16 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X0)) (X0 ◇ (X0 ◇ X1))]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X1 X2]
    conv => enter [1]; rw [l20 X0 X1 X2]
  have l24 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41797 X1 (X2 ◇ (X2 ◇ X0)) X0]
    conv => enter [1]; rw [← l22 X1 X2 X0]
  have l25 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l24 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X0)) (X0 ◇ X0)]
  have l26 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l25 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X0) (X0 ◇ X0)]
  have l27 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l26 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 (X0 ◇ X0)]
  have l28 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l27 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← l23 X2 X0 X0]
  have l29 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l28 X1 X2 X0]
    conv => enter [1, 2]; rw [← l18 X2 X0]
  have l30 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l31 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l30 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l32 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l31 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l29 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l33 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 sK0]
    conv => enter [1]; rw [← l32 sK0 sK1 X0 sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l34 x y z]

@[equational_result]
theorem Equation327_implies_Equation41800 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41800 G := by
  intro x y z w
  conv => enter [1]; rw [h327 x y (z ◇ (z ◇ w))]

theorem Equation4512_41800_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41800 : Equation41800 G) : Equation327 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41800 X2 X0 X1 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h41800 X0 X1 X1 X2]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41800 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) X0 (X0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l3 x y z]

@[equational_result]
theorem Equation327_implies_Equation41801 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41801 G := by
  intro x y z w
  conv => enter [1]; rw [h327 x y (z ◇ (w ◇ x))]

theorem Equation4512_41801_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41801 : Equation41801 G) : Equation327 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [h41801 X4 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h41801 X0 X1 X2 X3]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41801 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1))))]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2 X3 X4]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← l0 X1 X2 X3 X0 X0]
  have l6 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l4 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ X0)) X4]
  have l7 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = (X0 ◇ (X1 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l5 X0 X1 (X2 ◇ (X3 ◇ X0)) X4]
    conv => enter [1]; rw [← l6 X0 X1 X4 X2 X3]
  have l8 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X4)) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41801 X0 X1 X0 X0]
    conv => enter [1]; rw [l7 X0 X1 X0 X0 X4]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation327_implies_Equation41803 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41803 G := by
  intro x y z w
  conv => enter [1]; rw [h327 x y (z ◇ (w ◇ z))]

theorem Equation4512_41803_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41803 : Equation41803 G) : Equation327 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h41803 X3 X0 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h41803 X0 (X1 ◇ X2) X2 X1]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41803 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) X0 sK0 X0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l3 x y z]

@[equational_result]
theorem Equation327_implies_Equation41804 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41804 G := by
  intro x y z w
  conv => enter [1]; rw [h327 x y (z ◇ (w ◇ w))]

theorem Equation4512_41804_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41804 : Equation41804 G) : Equation327 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41804 X2 X0 X1 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h41804 X0 X1 (X2 ◇ X2) X2]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41804 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l3 x y z]

@[equational_result]
theorem Equation327_implies_Equation41805 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation41805 G := by
  intro x y z w u
  conv => enter [1]; rw [h327 x y (z ◇ (w ◇ u))]

theorem Equation4512_41805_implies_Equation327 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41805 : Equation41805 G) : Equation327 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41805 X2 X0 X1 X2 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h41805 X0 X1 X2 X2 X2]
  have l1 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h41805 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X1 ◇ X2))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l3 x y z]

@[equational_result]
theorem Equation329_implies_Equation3330 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3330 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK1]
    conv => enter [1]; rw [h329 sK0 (sK1 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation3330_4512_implies_Equation329 (G : Type*) [Magma G] (h3330 : Equation3330 G) (h4512 : Equation4512 G) : Equation329 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h3330 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X3 X2 X0 : G, (X3 ◇ X2) = (X3 ◇ (X0 ◇ X2)) := by
    intro X3 X2 X0
    conv => enter [1]; rw [l0 X3 X2 X0 X3]
    conv => enter [1, 2]; rw [← h3330 X0 X2 X3]
  have l2 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h3330 sK2 X0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ X0)]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (sK2 ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 (sK2 ◇ sK1) X0 X0]
    conv => enter [1]; rw [← l2 sK2 X0 sK1]
  have l4 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l3 sK2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) sK1]
  have l5 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h3330 sK0 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (X0 ◇ X0)]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l1 (sK0 ◇ (sK2 ◇ sK1)) X0 X0]
    conv => enter [1]; rw [← l5 sK0 X0 sK2 sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [← l4 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation329_implies_Equation3338 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3338 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h329 sK1 sK2 sK0]
    conv => enter [1]; rw [h329 sK1 (sK0 ◇ sK2) sK3]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation3338_4512_implies_Equation329 (G : Type*) [Magma G] (h3338 : Equation3338 G) (h4512 : Equation4512 G) : Equation329 G := by
  have l0 : ∀ X2 sK1 X0 X1 sK2 : G, (X2 ◇ sK1) = (X2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro X2 sK1 X0 X1 sK2
    conv => enter [1]; rw [h3338 X2 sK1 (X0 ◇ X1) sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK2 ◇ sK1)]
  have l1 : ∀ X2 sK2 sK1 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ sK1) := by
    intro X2 sK2 sK1
    conv => enter [1]; rw [h3338 X2 (sK2 ◇ sK1) X2 X2]
    conv => enter [1]; rw [← l0 X2 sK1 X2 X2 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

@[equational_result]
theorem Equation329_implies_Equation3312 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation3312 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h329 sK0 sK2 sK1]
    conv => enter [1]; rw [h329 sK0 (sK1 ◇ sK2) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h329 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [h329 x y z]
  conv => enter [1]; rw [l1 x z y]

theorem Equation3312_4512_implies_Equation329 (G : Type*) [Magma G] (h3312 : Equation3312 G) (h4512 : Equation4512 G) : Equation329 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h3312 X2 (X0 ◇ (X3 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h3312 X0 X1 X3]
  have l1 : ∀ X2 X1 X0 X3 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ X1))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h3312 X2 X1 X0]
    conv => enter [1]; rw [← l0 X2 X0 X3 X1]
  have l2 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1, 2, 2]; rw [h3312 X0 sK1 sK2]
    conv => enter [1]; rw [← h3312 X1 (X0 ◇ (sK2 ◇ sK1)) X0]
  have l3 : ∀ X1 sK1 X0 sK2 : G, (X1 ◇ sK1) = (X1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X1 sK1 X0 sK2
    conv => enter [1]; rw [h3312 X1 sK1 X0]
    conv => enter [1]; rw [l2 X1 X0 sK1 sK2]
  have l4 : ∀ X2 sK1 X0 X1 sK2 : G, (X2 ◇ sK1) = (X2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro X2 sK1 X0 X1 sK2
    conv => enter [1]; rw [l3 X2 sK1 (X0 ◇ X1) sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK2 ◇ sK1)]
  have l5 : ∀ X2 sK2 sK1 : G, (X2 ◇ (sK2 ◇ sK1)) = (X2 ◇ sK1) := by
    intro X2 sK2 sK1
    conv => enter [1]; rw [l1 X2 (sK2 ◇ sK1) X2 X2]
    conv => enter [1]; rw [← l4 X2 sK1 X2 X2 sK2]
  intro x y z
  conv => enter [1]; rw [← l5 x z y]

@[equational_result]
theorem Equation329_implies_Equation41811 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41811 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [h329 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41811_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41811 : Equation41811 G) : Equation329 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41811 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (sK2 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h41811 sK2 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 sK1]
  have l2 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h41811 sK0 (sK2 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41811 X0 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 2, 2]; rw [← h41811 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41811 X1 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41811 (X0 ◇ X0) X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X0]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))]
  have l8 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l6 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l10 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l1 sK2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ sK1)]
  have l11 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l1 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l10 sK2 sK1]
  have l12 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ sK1)]
  have l13 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l11 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) X0]
  have l14 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l12 sK0 sK2 sK1]
  have l15 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ sK1) ◇ X0) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 1]; rw [l14 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l19 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK2 sK1 (sK2 ◇ sK1)]
  have l20 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l19 sK0 sK2 sK1]
    conv => enter [1]; rw [← l9 sK0 sK2 sK1 (sK2 ◇ sK1)]
  have l21 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l20 sK0 sK2 sK1]
  have l22 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l20 sK0 sK2 sK1]
  have l23 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l22 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l24 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l1 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [← l13 sK2 sK1 sK1]
  have l25 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l24 sK2 sK1]
    conv => enter [1]; rw [← l13 sK2 sK1 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 sK1 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1 sK1]
  have l28 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h41811 X1 X1 X0]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l32 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41811 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 2, 2]; rw [← l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1 X0]
  have l34 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l21 sK0 sK2 sK1]
    conv => enter [1]; rw [← l15 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1)) sK0]
  have l35 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l14 sK2 sK1 sK0]
    conv => enter [1]; rw [l34 sK2 sK0 sK1]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41811 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l23 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
  have l37 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l36 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l21 sK0 sK2 sK1]
  have l38 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK2 sK1]
    conv => enter [1]; rw [l37 sK0 sK1 sK2 X0]
  have l39 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l38 sK0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l35 sK2 sK1 sK0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l3 sK1 sK1 (sK0 ◇ sK1)]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0]
  have l42 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ sK1)]
  have l43 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 sK1]
    conv => enter [1]; rw [l42 sK2 sK1 sK0]
  have l44 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l25 sK2 sK1]
    conv => enter [1]; rw [l43 sK2 sK1 sK0]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l44 sK2 sK1 sK0]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l46 x y z]

@[equational_result]
theorem Equation329_implies_Equation41815 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41815 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h329 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [h329 sK0 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41815_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41815 : Equation41815 G) : Equation329 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h41815 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41815 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))]
  have l4 : ∀ X0 X1 X3 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l3 X0 X1 X3 X0]
    conv => enter [1]; rw [← l2 X0 X3 X1 X0]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l4 sK2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [← l5 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation329_implies_Equation41819 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41819 G := by
  have l0 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h329 sK1 (sK0 ◇ sK2) sK1]
    conv => enter [1]; rw [h329 sK1 (sK1 ◇ (sK0 ◇ sK2)) sK3]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h329 sK1 sK2 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41819_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41819 : Equation41819 G) : Equation329 G := by
  have l0 : ∀ X3 X2 X4 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X4 X0 X1
    conv => enter [1]; rw [h41819 X3 X2 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l0 X3 X2 X3 X3 X1]
    conv => enter [1]; rw [← h41819 X3 (X1 ◇ X2) X3 X3]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation329_implies_Equation41828 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41828 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h329 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← h329 sK1 sK1 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK1]
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41828_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41828 : Equation41828 G) : Equation329 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41828 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
  have l1 : ∀ X3 X2 X0 : G, (X3 ◇ X2) = (X3 ◇ (X0 ◇ X2)) := by
    intro X3 X2 X0
    conv => enter [1]; rw [l0 X3 X2 X0 X3]
    conv => enter [1, 2]; rw [← h41828 X0 X2 X3]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation329_implies_Equation41832 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41832 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h329 sK2 sK1 sK2]
    conv => enter [1]; rw [h329 sK2 (sK2 ◇ sK1) sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41832_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41832 : Equation41832 G) : Equation329 G := by
  have l0 : ∀ X1 sK1 X0 sK2 : G, (X1 ◇ (sK1 ◇ X0)) = (X1 ◇ (sK2 ◇ ((sK1 ◇ X0) ◇ ((sK2 ◇ sK1) ◇ X0)))) := by
    intro X1 sK1 X0 sK2
    conv => enter [1]; rw [h41832 X1 (sK1 ◇ X0) sK2]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK2 sK1 X0]
  have l1 : ∀ X1 sK2 sK1 X0 sK0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (X1 ◇ (sK0 ◇ (((sK2 ◇ sK1) ◇ X0) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)))) := by
    intro X1 sK2 sK1 X0 sK0
    conv => enter [1]; rw [h41832 X1 ((sK2 ◇ sK1) ◇ X0) sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK2 ◇ sK1) X0]
  have l2 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41832 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41832 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l4 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h41832 X0 (sK2 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
  have l5 : ∀ X1 sK2 sK1 X0 sK0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0))))) := by
    intro X1 sK2 sK1 X0 sK0
    conv => enter [1]; rw [l1 X1 sK2 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ sK1) X0 ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l6 : ∀ X1 sK1 X0 sK2 : G, (X1 ◇ (sK1 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK1 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))))) := by
    intro X1 sK1 X0 sK2
    conv => enter [1]; rw [l0 X1 sK1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 X0 ((sK2 ◇ sK1) ◇ X0)]
  have l7 : ∀ X1 sK2 sK1 X0 sK0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)))) := by
    intro X1 sK2 sK1 X0 sK0
    conv => enter [1]; rw [l5 X1 sK2 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK1) (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0))]
  have l8 : ∀ X1 sK1 X0 sK2 : G, (X1 ◇ (sK1 ◇ X0)) = (X1 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0)))) := by
    intro X1 sK1 X0 sK2
    conv => enter [1]; rw [l6 X1 sK1 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (X0 ◇ ((sK2 ◇ sK1) ◇ X0))]
  have l9 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ X0) = (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [h41832 X1 X0 (X1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l7 X1 sK2 sK1 X0 X1]
  have l10 : ∀ X1 X0 sK1 : G, (X1 ◇ X0) = (X1 ◇ (sK1 ◇ X0)) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h41832 X1 X0 (X1 ◇ sK1)]
    conv => enter [1]; rw [← l8 X1 sK1 X0 X1]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 (sK0 ◇ sK1) sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK1)]
  have l12 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l4 (sK0 ◇ (sK2 ◇ sK1)) sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK2 sK1]
  have l14 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l10 sK0 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 (sK0 ◇ (sK2 ◇ sK1)) sK2 sK1 sK0]
  have l16 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l14 sK0 sK2 sK1]
    conv => enter [1]; rw [← l4 (sK0 ◇ sK1) sK2 sK1 sK0]
  have l17 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h41832 X0 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
  have l19 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l18 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l9 (sK0 ◇ (sK2 ◇ sK1)) X0 sK2 sK1]
  have l20 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l17 X0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l9 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ sK1) sK2 sK1]
  have l21 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l20 X0 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l22 : ∀ X0 sK1 sK2 : G, (X0 ◇ sK1) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK1 X0]
    conv => enter [1]; rw [← l21 X0 sK2 sK1 X0]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← l19 sK0 sK1 (sK2 ◇ sK1) sK2]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1 sK0]
    conv => enter [1]; rw [← l22 (sK0 ◇ sK1) sK1 sK0]
  have l25 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l16 sK0 sK2 sK1]
    conv => enter [1]; rw [← l22 (sK0 ◇ sK1) sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l26 x y z]

@[equational_result]
theorem Equation329_implies_Equation41836 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41836 G := by
  have l0 : ∀ sK1 sK3 sK2 sK0 : G, (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK3 sK2 sK0
    conv => enter [1]; rw [← h329 sK1 (sK2 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1]; rw [← h329 sK1 (sK0 ◇ sK2) sK2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h329 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK1 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41836_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41836 : Equation41836 G) : Equation329 G := by
  have l0 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X2) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [h41836 X4 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l1 : ∀ X4 X2 X0 : G, (X4 ◇ X2) = (X4 ◇ (X0 ◇ X2)) := by
    intro X4 X2 X0
    conv => enter [1]; rw [l0 X4 X2 X4 (X0 ◇ X2) X0]
    conv => enter [1]; rw [← h41836 X4 (X0 ◇ X2) X4 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation329_implies_Equation41845 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41845 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK2 ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h329 sK2 (sK1 ◇ sK1) sK2]
    conv => enter [1]; rw [← h329 sK2 sK1 sK1]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h329 sK2 sK1 sK1]
    conv => enter [1]; rw [← l0 sK2 sK1]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l1 sK2 sK1]
    conv => enter [1]; rw [← h329 sK0 (sK1 ◇ sK1) sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK1]
    conv => enter [1]; rw [← l2 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41845_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41845 : Equation41845 G) : Equation329 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X3 ◇ (X3 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h41845 X2 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X3]
    conv => enter [1, 2, 2, 2]; rw [← h41845 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41845 X1 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41845 (X0 ◇ X0) X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41845 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ (X2 ◇ (X1 ◇ X1))) X3]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ (X1 ◇ X1)) X3]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X0]
  have l5 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l0 X2 X0 X1 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l6 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l7 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l5 X2 X0 X1 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X1]
  have l8 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l6 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X3]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l7 X2 X0 X1 X3]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X1 X1 X1]
  have l10 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
  have l11 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l9 X2 X0 X1 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 X0 X1]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 X0 X1 X2]
    conv => enter [1]; rw [← l10 X2 X0 (X1 ◇ X1) X2]
  have l13 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41845 X2 X1 X0]
    conv => enter [1]; rw [l12 X2 X0 X1]
  have l14 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41845 X2 X1 X0]
    conv => enter [1, 2]; rw [← l13 X0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

@[equational_result]
theorem Equation329_implies_Equation41853 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41853 G := by
  have l0 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2))) = (sK3 ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h329 sK3 (sK0 ◇ sK2) sK3]
    conv => enter [1]; rw [← h329 sK3 sK2 sK0]
  have l1 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h329 sK3 sK2 sK0]
    conv => enter [1]; rw [← l0 sK3 sK0 sK2]
  have l2 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [← l1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h329 sK1 (sK0 ◇ sK2) sK3]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h329 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_41853_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41853 : Equation41853 G) : Equation329 G := by
  have l0 : ∀ X3 X2 X4 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X4 X0 X1
    conv => enter [1]; rw [h41853 X3 X2 X4 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l0 X3 X2 X3 X3 X1]
    conv => enter [1]; rw [← h41853 X3 (X1 ◇ X2) X3 X3]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation329_implies_Equation41863 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41863 G := by
  have l0 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h329 sK1 (sK0 ◇ (sK2 ◇ sK2)) sK3]
    conv => enter [1]; rw [← h329 sK1 (sK2 ◇ sK2) sK0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h329 sK1 sK2 sK2]
    conv => enter [1]; rw [← l0 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41863_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41863 : Equation41863 G) : Equation329 G := by
  have l0 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [h41863 X4 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l1 : ∀ X4 X3 X0 : G, (X4 ◇ X3) = (X4 ◇ (X0 ◇ X3)) := by
    intro X4 X3 X0
    conv => enter [1]; rw [l0 X4 X3 X0 X4 X4]
    conv => enter [1, 2]; rw [← h41863 X0 X3 X4 X4]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation329_implies_Equation41868 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41868 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ sK2) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [h329 sK3 sK2 sK3]
    conv => enter [1]; rw [h329 sK3 (sK3 ◇ sK2) sK0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h329 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l0 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41868_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41868 : Equation41868 G) : Equation329 G := by
  have l0 : ∀ X4 X3 X2 X0 X1 : G, (X4 ◇ X3) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X3 X2 X0 X1
    conv => enter [1]; rw [h41868 X4 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [h41868 X4 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
  have l2 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [l1 X4 X3 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l3 : ∀ X4 X3 X1 : G, (X4 ◇ X3) = (X4 ◇ (X1 ◇ X3)) := by
    intro X4 X3 X1
    conv => enter [1]; rw [l2 X4 X3 X4 X1 X4]
    conv => enter [1]; rw [← l0 X4 (X1 ◇ X3) X4 X1 X4]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation329_implies_Equation41873 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41873 G := by
  have l0 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h329 sK1 (sK0 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1, 2]; rw [← h329 sK0 sK2 sK0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h329 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41873_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41873 : Equation41873 G) : Equation329 G := by
  have l0 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ X3) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [h41873 X4 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
  have l1 : ∀ X4 X3 X0 : G, (X4 ◇ X3) = (X4 ◇ (X0 ◇ X3)) := by
    intro X4 X3 X0
    conv => enter [1]; rw [l0 X4 X3 X4 X0 X0]
    conv => enter [1]; rw [← h41873 X4 (X0 ◇ X3) X4 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation329_implies_Equation41878 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41878 G := by
  have l0 : ∀ sK2 sK4 sK1 sK0 sK3 : G, (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h329 sK2 (sK1 ◇ (sK0 ◇ sK3)) sK4]
    conv => enter [1]; rw [← h329 sK2 (sK0 ◇ sK3) sK1]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h329 sK2 sK3 sK0]
    conv => enter [1]; rw [← l0 sK2 sK4 sK1 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]

theorem Equation4512_41878_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41878 : Equation41878 G) : Equation329 G := by
  have l0 : ∀ X5 X4 X0 X1 X2 X3 : G, (X5 ◇ X4) = (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X5 X4 X0 X1 X2 X3
    conv => enter [1]; rw [h41878 X5 X4 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l1 : ∀ X5 X4 X3 : G, (X5 ◇ X4) = (X5 ◇ (X3 ◇ X4)) := by
    intro X5 X4 X3
    conv => enter [1]; rw [l0 X5 X4 X5 X5 X5 X3]
    conv => enter [1]; rw [← h41878 X5 (X3 ◇ X4) X5 X5 X5]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation329_implies_Equation41739 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41739 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h329 sK0 sK2 sK1]
    conv => enter [1]; rw [h329 sK0 (sK1 ◇ sK2) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h329 sK0 sK2 sK1]
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h329 sK0 sK2 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h329 sK0 sK2 sK1]
    conv => enter [1]; rw [l3 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [h329 x y z]
  conv => enter [1]; rw [l4 x z y]

theorem Equation4512_41739_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41739 : Equation41739 G) : Equation329 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41739 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ X2)) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l0 X3 X2 X3 X1]
    conv => enter [1]; rw [← h41739 X3 (X1 ◇ X2) X3]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation329_implies_Equation41761 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41761 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h329 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [h329 sK1 sK2 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h329 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1, 2]; rw [← h329 sK1 sK2 sK1]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h329 sK0 sK2 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l2 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [l3 x z y]

theorem Equation4512_41761_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41761 : Equation41761 G) : Equation329 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h41761 X2 (X0 ◇ (X3 ◇ (X3 ◇ X1))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41761 X0 X1 X3]
  have l1 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h41761 sK2 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK1 ◇ X0)]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41761 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2)))]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ X2))]
  have l4 : ∀ X2 X1 X0 X3 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1]; rw [← l0 X2 X0 X3 X1]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← l4 X0 X2 X1 X0]
  have l7 : ∀ X1 sK0 sK2 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (X1 ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro X1 sK0 sK2 sK1 X0
    conv => enter [1]; rw [h41761 X1 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1, 2, 2]; rw [← h41761 X0 (sK2 ◇ sK1) sK0]
  have l8 : ∀ X1 X0 sK0 sK2 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ sK1))))) := by
    intro X1 X0 sK0 sK2 sK1
    conv => enter [1]; rw [h41761 X1 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41761 X0 (sK2 ◇ sK1) sK0]
  have l9 : ∀ X1 X0 sK0 sK2 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (X1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X0 sK0 sK2 sK1
    conv => enter [1]; rw [l8 X1 X0 sK0 sK2 sK1]
    conv => enter [1]; rw [← h41761 X1 (sK2 ◇ sK1) X0]
  have l10 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1, 2, 2]; rw [h41761 sK1 sK1 sK2]
    conv => enter [1]; rw [← l1 sK2 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1]
  have l11 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ X0))) = (X1 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ X0)))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [h41761 X1 ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) sK2]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK2 X0 sK1]
  have l12 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ X0) = (X1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [h41761 X1 X0 sK2]
    conv => enter [1]; rw [← l11 X1 sK2 sK1 X0]
  have l13 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l6 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l10 sK2 sK1]
  have l14 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l12 sK2 sK1 sK2 sK1]
    conv => enter [1]; rw [← l13 sK2 sK1]
  have l15 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l14 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l16 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l15 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l17 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h41761 X0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l15 sK2 sK1]
  have l18 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l15 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
  have l19 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l17 X0 sK2 sK1]
    conv => enter [1]; rw [← l7 X0 sK0 sK2 sK1 (sK2 ◇ sK1)]
  have l20 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l16 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
  have l21 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41761 (sK2 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [← l18 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l22 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (X1 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [h41761 X1 ((sK2 ◇ sK1) ◇ X0) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l18 sK2 sK1 X0]
  have l23 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (X1 ◇ X0) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [l22 X1 sK2 sK1 X0]
    conv => enter [1]; rw [← h41761 X1 X0 (sK2 ◇ sK1)]
  have l24 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((X0 ◇ X1) ◇ (sK2 ◇ sK1)) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1, 2]; rw [← l19 X1 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 X0 X1 (sK2 ◇ sK1)]
  have l25 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1]; rw [l24 X0 X1 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK1)]
  have l26 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← l9 X0 X1 X0 sK2 sK1]
    conv => enter [1]; rw [l25 X0 X1 X0 sK2 sK1]
  have l27 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l21 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41761 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l21 sK2 sK1 sK0]
  have l29 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41761 X0 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← l28 X0 sK0 sK1 X0]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l23 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [l27 sK0 sK2 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 (sK0 ◇ (sK2 ◇ sK1)) sK1 sK0]
  have l32 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h41761 (sK2 ◇ sK1) sK1 sK2]
    conv => enter [1]; rw [l23 (sK2 ◇ sK1) sK2 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l33 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l32 sK2 sK1]
    conv => enter [1]; rw [← l26 (sK2 ◇ sK1) sK2 sK1 sK2]
  have l34 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l15 sK2 sK1]
    conv => enter [1]; rw [← l33 sK2 sK1]
  have l35 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l34 sK2 sK1]
  have l36 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l16 sK0 sK2 sK1]
    conv => enter [1]; rw [← l35 sK0 sK2 sK1]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← l36 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l37 x y z]

@[equational_result]
theorem Equation329_implies_Equation41749 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41749 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK2]
    conv => enter [1]; rw [h329 sK0 (sK2 ◇ sK1) sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h329 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41749_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41749 : Equation41749 G) : Equation329 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41749 X2 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h41749 (X0 ◇ (X1 ◇ X0)) X0 X1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41749 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h41749 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (X0 ◇ sK1)]
  have l3 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h41749 sK0 (sK2 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK1) (X0 ◇ (sK2 ◇ sK1))]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1]; rw [← h41749 X2 X0 (X1 ◇ X0)]
  have l6 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ (((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [h41749 X0 ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0 sK2 sK1 sK0]
  have l7 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l6 X0 sK0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK1))]
  have l8 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [h41749 X0 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l7 X0 sK0 sK2 sK1]
  have l9 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h41749 X0 ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK2 sK1 sK0]
  have l10 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l9 X0 sK2 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ sK1) (sK0 ◇ sK1) (sK2 ◇ sK1)]
  have l11 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h41749 X0 (sK2 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l10 X0 sK2 sK1 sK0]
  have l12 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41749 X0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 sK1 sK0]
  have l13 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l12 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41749 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l13 X0 sK0 sK1]
  have l15 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41749 X0 ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 sK1 sK2]
  have l16 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l15 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK1) (sK0 ◇ sK1)]
  have l17 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41749 X0 (sK0 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l16 X0 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l8 sK0 sK0 sK2 sK1]
  have l19 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1 sK2]
    conv => enter [1]; rw [← l11 sK2 sK2 sK1 sK2]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41749 X0 (sK0 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l11 (sK0 ◇ sK1) sK2 sK1 sK0]
  have l21 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l20 X0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l17 X0 sK0 sK1 X0]
  have l22 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l19 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) X0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l14 sK0 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l21 sK1 sK0 sK1]
    conv => enter [1]; rw [← h41749 sK1 sK1 sK0]
  have l26 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h41749 sK1 sK1 sK0]
  have l27 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l26 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 sK1]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0 sK1]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l29 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l21 sK1 sK0 sK1]
    conv => enter [1]; rw [l27 sK2 sK1 sK0]
  have l30 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l29 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [l28 sK1 sK2]
  have l31 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l30 sK2 sK1]
  have l32 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l31 sK2 sK1]
    conv => enter [1]; rw [← l22 sK2 sK1 sK1]
  have l33 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l32 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) sK1]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l33 sK0 sK2 sK1]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l24 sK0 sK1 (sK0 ◇ (sK2 ◇ sK1))]
  have l36 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41749 X0 X1 X0]
    conv => enter [1, 2]; rw [l5 X0 X1 X0]
  have l37 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l36 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X0 X1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1 sK0]
    conv => enter [1]; rw [l37 sK0 (sK0 ◇ sK1)]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [l38 sK0 sK1]
  have l40 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l39 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l41 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [← l40 sK0 sK1 X0]
  have l42 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
    conv => enter [1]; rw [l41 sK0 (sK0 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l18 sK0 sK2 sK1]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [← l42 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l43 x y z]

@[equational_result]
theorem Equation329_implies_Equation41757 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41757 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ sK2) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h329 X0 (sK2 ◇ sK2) sK1]
    conv => enter [1]; rw [← h329 X0 sK2 sK2]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
    conv => enter [1]; rw [h329 sK0 (sK1 ◇ (sK2 ◇ sK2)) sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41757_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41757 : Equation41757 G) : Equation329 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41757 X2 (X0 ◇ (X1 ◇ X1)) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41757 (X0 ◇ (X1 ◇ X1)) X1 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41757 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41757 X0 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h41757 X0 X1 (X1 ◇ X1)]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X1]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l1 X2 X1 X0 X1]
    conv => enter [1]; rw [← l4 X2 X0 X1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l7 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (X0 ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l2 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ X0)]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l2 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l9 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l2 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ X0)]
  have l10 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l5 sK0 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l9 sK0 sK2 sK1 X0]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l12 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l5 sK2 X0 sK1]
    conv => enter [1]; rw [l7 sK2 sK1 X0]
  have l13 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1, 2]; rw [h41757 (sK2 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l10 sK0 ((sK2 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X0))) sK2 sK1]
  have l14 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l13 sK0 sK2 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (X1 ◇ (X0 ◇ X0))]
  have l15 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l5 (sK0 ◇ (sK2 ◇ sK1)) X0 sK0]
    conv => enter [1]; rw [← l14 sK0 sK2 sK1 X0 sK0]
  have l16 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l10 sK0 X0 sK2 sK1]
  have l17 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ (sK1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h41757 sK1 X0 X1]
    conv => enter [1]; rw [← l11 sK0 (sK1 ◇ (X1 ◇ (X0 ◇ X0))) sK1]
  have l18 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41757 X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l11 sK0 sK1 sK1]
  have l19 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l17 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X1 ◇ (X0 ◇ X0))]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 X0 sK0]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [← l11 sK0 X0 sK1]
  have l22 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l2 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l21 sK0 sK1 (sK0 ◇ sK1)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l21 sK0 sK1 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l24 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l18 X0 sK1 sK0]
    conv => enter [1]; rw [l22 X0 sK0 sK1]
  have l25 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l24 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l23 sK0 sK1]
  have l26 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) = ((X0 ◇ sK1) ◇ X1) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [← l25 X0 sK1 sK0]
  have l27 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l26 X0 sK0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 sK1 X1]
  have l28 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro X0 sK0 X1 sK1
    conv => enter [1, 2]; rw [← l21 sK0 sK1 X1]
    conv => enter [1]; rw [l27 X0 sK0 sK1 X1]
  have l29 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l25 sK2 sK1 sK0]
    conv => enter [1]; rw [l12 sK2 sK1 sK1]
  have l30 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l29 sK2 sK0 sK1]
    conv => enter [1]; rw [l28 (sK2 ◇ sK1) sK1 sK1 sK0]
  have l31 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l25 sK2 sK1 sK0]
    conv => enter [1]; rw [l30 sK2 sK0 sK1]
  have l32 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l31 sK2 sK1 sK2]
    conv => enter [1]; rw [← l25 (sK2 ◇ sK1) sK1 sK2]
  have l33 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l32 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) sK1]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l16 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [← l33 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l34 x y z]

@[equational_result]
theorem Equation329_implies_Equation41765 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation41765 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ sK0) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h329 X0 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [← h329 X0 sK0 sK3]
  have l1 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [← l0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h329 sK1 (sK2 ◇ (sK3 ◇ sK0)) sK1]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41765_implies_Equation329 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41765 : Equation41765 G) : Equation329 G := by
  have l0 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ X3) = (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [h41765 X4 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X4 X3 X2 : G, (X4 ◇ X3) = (X4 ◇ (X2 ◇ X3)) := by
    intro X4 X3 X2
    conv => enter [1]; rw [l0 X4 X3 X4 X4 X2]
    conv => enter [1]; rw [← h41765 X4 (X2 ◇ X3) X4 X4]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation3345_4512_implies_Equation332 (G : Type*) [Magma G] (h3345 : Equation3345 G) (h4512 : Equation4512 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h3345 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h3345 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [h3345 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h3345 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l7 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h3345 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l10 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 (sK1 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [l16 sK0 sK1]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3345 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [l21 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← h3345 (sK0 ◇ sK1) sK0]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l28 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l26 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK0 sK1]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l28 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l27 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1, 2]; rw [l19 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l33 sK0 sK1 X0]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1, 2]; rw [← l36 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK0) sK1]
  have l47 : ∀ sK0 X0 sK1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ sK1) = (sK1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3345 ((sK0 ◇ sK0) ◇ X0) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
  have l48 : ∀ sK0 X0 sK1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l47 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [l43 sK0 sK1 sK1]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK1 (sK0 ◇ sK1)]
  have l51 : ∀ sK0 X0 sK1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l48 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l50 sK1 sK0]
  have l53 : ∀ sK0 X0 sK1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l51 sK0 X0 sK1]
    conv => enter [1]; rw [← h3345 X0 (sK1 ◇ (sK0 ◇ sK0))]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l52 sK1 sK0]
  have l55 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l53 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 sK1]
  have l56 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l57 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) sK1 X0]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1)]
    conv => enter [1, 2]; rw [← l49 sK1 sK0]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l58 sK0 sK1]
    conv => enter [1]; rw [← l55 (sK1 ◇ (sK0 ◇ sK0)) sK1 sK0]
  have l60 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [← l59 sK0 sK1]
  have l61 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l60 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)))]
  have l63 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [← l57 sK0 sK1 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1))]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 ((sK0 ◇ sK0) ◇ sK1)]
  have l65 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l64 sK1 sK0]
    conv => enter [1]; rw [← l61 sK1 sK0 ((sK0 ◇ sK0) ◇ sK1)]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l65 sK1 sK0]
    conv => enter [1]; rw [← l56 sK1 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l66 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l67 x y]

theorem Equation332_4512_implies_Equation3345 (G : Type*) [Magma G] (h332 : Equation332 G) (h4512 : Equation4512 G) : Equation3345 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h332 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h332 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h332 X0 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h332 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h332 X0 X1]
    conv => enter [1]; rw [l3 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h332 X0 X1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h332 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]
  conv => enter [1]; rw [l7 y x]

theorem Equation3345_4512_implies_Equation335 (G : Type*) [Magma G] (h3345 : Equation3345 G) (h4512 : Equation4512 G) : Equation335 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h3345 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ sK1) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h3345 (sK0 ◇ sK1) sK0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h3345 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h3345 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ sK0) = (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3345 (sK1 ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l13 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ sK0) = (sK0 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l12 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l14 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ sK0) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l13 sK1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l15 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ sK0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l14 sK1 X0 sK0]
    conv => enter [1]; rw [← h3345 X0 (sK0 ◇ sK1)]
  have l16 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l15 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK1 X0 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h3345 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l11 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0 (sK1 ◇ sK0)]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [h3345 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l18 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK1 ◇ sK0)]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l20 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l24 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK0]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l25 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 sK1]
    conv => enter [1, 2]; rw [← l37 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l38 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [← l39 sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l44 sK1 sK0]
  have l46 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l47 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l45 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l47 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l46 sK0 sK1 (sK0 ◇ sK1)]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1, 1]; rw [l50 sK0 sK1]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h3345 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l53 sK1 sK0]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l16 (sK0 ◇ sK1) sK0 sK1]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l55 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l56 x y]

theorem Equation335_4512_implies_Equation3345 (G : Type*) [Magma G] (h335 : Equation335 G) (h4512 : Equation4512 G) : Equation3345 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h335 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h335 sK1 sK0]
    conv => enter [1]; rw [← h335 (sK0 ◇ sK1) sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l7 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h335 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h335 (sK1 ◇ sK0) (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h335 sK0 sK1]
    conv => enter [1, 2]; rw [l18 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h335 sK1 sK0]
    conv => enter [1, 2]; rw [l18 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l20 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1, 2]; rw [l21 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation3345_4512_implies_Equation3352 (G : Type*) [Magma G] (h3345 : Equation3345 G) (h4512 : Equation4512 G) : Equation3352 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h3345 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h3345 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [h3345 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (((sK1 ◇ sK1) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h3345 (sK1 ◇ sK1) sK0]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h3345 sK0 sK1]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) sK0 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l8 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l9 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK1 X0 sK0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ sK0) = (sK0 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h3345 ((sK1 ◇ sK1) ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l16 : ∀ sK1 X0 sK0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l15 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l17 : ∀ sK1 X0 sK0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l16 sK1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))]
  have l18 : ∀ sK1 X0 sK0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l17 sK1 X0 sK0]
    conv => enter [1]; rw [← h3345 X0 (sK0 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l18 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) X0 sK0]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l14 sK1 sK0]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0 ((sK1 ◇ sK1) ◇ sK0)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) sK0 X0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l22 sK0 sK1]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l23 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l29 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l35 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ sK0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3345 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l36 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) X0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l37 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))]
  have l38 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1]; rw [← h3345 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l39 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l38 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) X0 sK0]
  have l40 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l41 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l44 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ X0) ◇ sK1) = (sK1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ X0) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l45 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ X0) ◇ sK1) = (sK1 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l44 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l46 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ X0) ◇ sK1) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l45 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l47 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ X0) ◇ sK1) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l46 sK0 X0 sK1]
    conv => enter [1]; rw [← h3345 X0 (sK1 ◇ sK0)]
  have l48 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l47 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 sK1]
  have l49 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 (sK1 ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK1)]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [l40 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [← h3345 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [l41 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← h3345 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [h3345 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l43 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 (sK0 ◇ sK1)]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 sK1 sK0]
    conv => enter [1]; rw [← l56 sK0 sK1]
  have l58 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l57 sK0 sK1]
  have l59 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [← l51 sK1 sK0]
  have l60 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l59 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK0) X0]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 X0]
    conv => enter [1, 1]; rw [← l54 sK0 sK1]
  have l62 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK0) X0]
  have l63 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h3345 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l65 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l66 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3345 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l67 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1]; rw [l65 sK1 sK0 X0]
  have l68 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l64 sK1 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1 (sK1 ◇ sK0)]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK0]
  have l70 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [l68 sK1 sK0]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l70 sK1 sK0]
    conv => enter [1]; rw [l58 sK1 sK0]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [← l71 sK0 sK1]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l66 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK0)]
  have l75 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK0) X0]
  have l76 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l72 sK0 sK1]
  have l77 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l76 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l78 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l77 sK1 sK0]
    conv => enter [1]; rw [l60 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l79 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l78 sK1 sK0]
    conv => enter [1, 2]; rw [← l42 sK1 sK0]
  have l80 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l79 sK1 sK0]
    conv => enter [1]; rw [← l63 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l81 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l80 sK1 sK0]
  have l82 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l73 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l83 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l74 sK0 sK1]
  have l84 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [l83 sK1 sK0]
    conv => enter [1, 2]; rw [← l42 sK1 sK0]
  have l85 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [l62 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l86 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l85 sK1 sK0]
  have l87 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 sK1]
    conv => enter [1]; rw [← l81 sK1 sK0]
  have l88 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l87 sK0 sK1]
  have l89 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l82 sK0 sK1]
  have l90 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l89 sK1 sK0]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l90 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l92 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1, 2]; rw [← l91 sK0 sK1]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1]
    conv => enter [1]; rw [l92 sK1 sK0]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [l93 sK0 sK1]
  have l95 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [l19 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ sK0)]
  have l96 : ∀ sK1 X0 sK0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ sK0) ◇ X1)) = ((X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l19 X0 sK0 sK1]
  have l97 : ∀ X0 sK0 sK1 : G, ((X0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((X0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3345 (X0 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l19 X0 sK0 sK1]
  have l98 : ∀ X0 sK0 sK1 : G, ((X0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l97 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l99 : ∀ sK1 X0 sK0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [l96 sK1 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l100 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l95 sK0 X0 sK1]
    conv => enter [1]; rw [← l39 X0 sK0 sK1]
  have l101 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l98 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 sK0 (sK1 ◇ sK1)]
  have l102 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← l99 sK1 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l103 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [← l100 sK0 X0 sK1]
  have l104 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l101 sK1 X0 sK0]
    conv => enter [1]; rw [← l102 X0 sK0 sK1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l105 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l104 X0 sK0 sK1]
  have l106 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l105 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK1))]
  have l107 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ ((X0 ◇ sK1) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [← l48 X0 sK1 sK0]
  have l108 : ∀ X0 sK1 sK0 : G, ((X0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((X0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h3345 (X0 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l48 X0 sK1 sK0]
  have l109 : ∀ X0 sK1 sK0 : G, ((X0 ◇ sK1) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l108 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 (X0 ◇ (sK1 ◇ sK0))]
  have l110 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ ((X0 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l107 sK0 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK0) X1]
  have l111 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l109 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 sK1 sK0]
  have l112 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ X1)) = (sK0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← l110 sK0 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l113 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l111 sK0 X0 sK1]
    conv => enter [1]; rw [← l112 X0 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
  have l114 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3345 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← l113 X0 sK1 sK0]
  have l115 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l114 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l116 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l67 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l114 sK1 sK0 X0]
  have l117 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l48 sK0 sK1 sK0]
  have l118 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l117 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l119 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l118 sK1 sK0]
    conv => enter [1]; rw [l115 sK1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l120 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l119 sK1 sK0]
    conv => enter [1]; rw [← l116 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l121 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l120 sK1 sK0]
    conv => enter [1]; rw [l106 sK0 sK1 sK0 (sK1 ◇ sK0)]
  have l122 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l121 sK1 sK0]
    conv => enter [1]; rw [← l103 (sK1 ◇ sK0) sK0 sK1]
  have l123 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l122 sK1 sK0]
    conv => enter [1]; rw [← l94 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l123 x y]
  conv => enter [1]; rw [l91 y x]

theorem Equation3352_4512_implies_Equation3345 (G : Type*) [Magma G] (h3352 : Equation3352 G) (h4512 : Equation4512 G) : Equation3345 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h3352 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3352 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h3352 X0 X0]
    conv => enter [1]; rw [← l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h3352 X0 X0]
    conv => enter [1]; rw [← l3 X0]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3352 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK1 sK0 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l4 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3352 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3352 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [← l15 sK1 sK0]
  have l17 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1]; rw [← l16 sK1 sK0 X0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3352 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 sK0 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l20 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation3345_4512_implies_Equation41886 (G : Type*) [Magma G] (h3345 : Equation3345 G) (h4512 : Equation4512 G) : Equation41886 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h3345 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (((sK1 ◇ sK0) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h3345 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h3345 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK0)]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [l7 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 sK1]
    conv => enter [1, 2]; rw [l20 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation4512_41886_implies_Equation3345 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41886 : Equation41886 G) : Equation3345 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l4 sK1 sK0 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41886 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41886 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [l10 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41886 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l12 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41886 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1, 2]; rw [l12 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41886 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41886 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1, 2]; rw [l12 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l10 sK1 sK0]
    conv => enter [1]; rw [l24 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1, 2]; rw [l12 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l23 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41886 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l23 sK0 sK1]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1))]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l41 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41886 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l26 sK1 sK0]
  have l42 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l43 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l42 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l44 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1]; rw [← l40 sK1 sK0]
  have l46 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l43 sK1 sK0 (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l46 sK1 sK0]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l47 sK1 sK0]
  have l49 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [← l48 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1, 2]; rw [l10 sK1 sK0]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← l51 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l54 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l55 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l33 sK1 sK0]
  have l56 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l55 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK1) X0]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l37 sK1 sK0]
  have l58 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l37 sK1 sK0]
  have l59 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK0) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l37 sK1 sK0]
  have l60 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l59 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l57 sK0 sK1]
  have l62 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l63 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l62 sK0 sK1 X0]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1, 2]; rw [← l45 sK1 sK0]
  have l65 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l66 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l65 sK1 sK0 X0]
  have l67 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l64 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l68 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l54 sK1 sK0 X0]
    conv => enter [1]; rw [l66 sK1 sK0 X0]
  have l69 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l27 sK1 sK0]
  have l70 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41886 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l27 sK1 sK0]
  have l71 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l70 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0)) (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l72 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l58 sK1 sK0]
    conv => enter [1]; rw [← l69 sK1 sK0]
  have l73 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l71 sK1 sK0]
    conv => enter [1, 2]; rw [l56 sK1 sK0 (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l74 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l72 sK1 sK0]
    conv => enter [1]; rw [← l54 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l75 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l73 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ sK1) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0)))]
  have l76 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l74 sK1 sK0]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l77 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l75 sK1 sK0]
    conv => enter [1]; rw [l60 sK0 sK1 (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l78 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l77 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ sK0)]
  have l79 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l78 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l56 sK1 sK0 ((sK1 ◇ sK0) ◇ sK0)]
  have l80 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l79 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) = (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1 ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))]
    conv => enter [1]; rw [← l80 sK1 sK0]
  have l82 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l83 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l56 sK1 sK0 sK0]
    conv => enter [1]; rw [← l82 sK0 sK1]
  have l84 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← l83 sK1 sK0]
  have l85 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l86 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l85 sK0 sK1]
  have l87 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l88 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l87 sK0 sK1]
    conv => enter [1]; rw [← l53 sK0 sK1]
  have l89 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l87 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l90 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l87 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l91 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41886 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l87 sK0 sK1]
  have l92 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l91 sK1 sK0]
    conv => enter [1]; rw [← l63 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1))]
  have l93 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l67 sK1 sK0]
    conv => enter [1]; rw [← l90 sK1 sK0]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l89 sK0 sK1]
    conv => enter [1, 2]; rw [← l45 sK1 sK0]
  have l95 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l68 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l92 sK1 sK0]
  have l96 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l97 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l95 sK0 sK1]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l98 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l96 sK0 sK1]
  have l99 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l97 sK0 sK1]
  have l100 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1]
    conv => enter [1]; rw [l98 sK0 sK1]
  have l101 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1]
    conv => enter [1]; rw [l99 sK0 sK1]
  have l102 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1, 2]; rw [← l93 sK1 sK0]
  have l103 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l93 sK1 sK0]
  have l104 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l93 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l105 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← l103 sK1 sK0]
  have l106 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l105 sK1 sK0]
    conv => enter [1]; rw [← l104 sK1 sK0 (sK0 ◇ sK1)]
  have l107 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41886 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l102 sK1 sK0]
  have l108 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l102 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l109 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l108 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l107 sK1 sK0]
  have l110 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l109 sK1 sK0]
    conv => enter [1]; rw [l76 sK1 sK0]
  have l111 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l101 sK0 sK1]
    conv => enter [1]; rw [← l110 sK1 sK0]
  have l112 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l111 sK0 sK1]
    conv => enter [1]; rw [← l54 sK1 sK0 (sK1 ◇ sK0)]
  have l113 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41886 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l106 sK1 sK0]
  have l114 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l106 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK1) X0]
  have l115 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [← l114 sK1 sK0 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l116 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l114 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l115 sK0 sK1]
  have l117 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l102 sK1 sK0]
    conv => enter [1]; rw [← l116 sK1 sK0]
  have l118 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l112 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l119 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l117 sK1 sK0]
    conv => enter [1]; rw [← l45 sK1 sK0]
  have l120 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l118 sK0 sK1]
    conv => enter [1]; rw [← l119 sK1 sK0]
  have l121 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 1]; rw [l120 sK1 sK0]
    conv => enter [1, 2]; rw [l120 sK1 sK0]
  have l122 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l100 sK0 sK1]
    conv => enter [1]; rw [← l121 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l122 x y]

theorem Equation3345_4512_implies_Equation41893 (G : Type*) [Magma G] (h3345 : Equation3345 G) (h4512 : Equation4512 G) : Equation41893 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h3345 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← h3345 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) = (((sK0 ◇ sK0) ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h3345 (sK0 ◇ sK0) sK1]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l5 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3345 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3345 (sK0 ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← h3345 X0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 X0 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK1]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [h3345 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l19 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← l11 sK1 sK0 (sK1 ◇ sK0)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 sK1]
    conv => enter [1]; rw [← l22 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l23 sK1 sK0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l24 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l24 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l26 sK0 sK1 X0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1 (sK0 ◇ sK1)]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK1) X0]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l30 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1, 2]; rw [← l29 sK0 sK1 (sK0 ◇ sK1)]
  have l34 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l31 sK0 sK1 X0]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l19 sK1 sK0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l17 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3345 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [h3345 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l41 sK1 sK0]
  have l43 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [← l10 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l43 sK1 sK0]
  have l45 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l44 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l50 sK0 sK1]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [← l25 sK0 sK1 (sK0 ◇ sK1)]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l52 sK1 sK0]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l53 sK1 sK0]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l49 sK1 sK0]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l57 sK0 sK1]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [l59 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [h3345 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l51 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l63 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l62 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l65 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l65 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1)]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l66 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l67 sK0 sK1]
  have l69 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [← l68 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1, 1]; rw [← l69 sK1 sK0]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l69 sK1 sK0]
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1, 2]; rw [← l69 sK1 sK0]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l65 sK1 sK0]
    conv => enter [1]; rw [← l70 sK0 sK1]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [← l72 sK1 sK0]
  have l74 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3345 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l71 sK1 sK0]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l69 sK1 sK0]
    conv => enter [1]; rw [← l74 sK0 sK1]
  have l76 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l73 sK1 sK0]
    conv => enter [1]; rw [l75 sK1 sK0]
  have l77 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l76 sK1 sK0]
  have l78 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l69 sK1 sK0]
    conv => enter [1]; rw [← l77 sK1 sK0]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l78 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l79 x y]

end Semigroup5
