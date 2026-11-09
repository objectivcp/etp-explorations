import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation4274_implies_Equation54683 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54683 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK2 ◇ sK0)]
  have l2 : ∀ X1 sK1 sK2 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK1 sK2 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK2 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK0)) sK1 sK2 sK0 X0]
  have l3 : ∀ X0 sK1 sK2 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro X0 sK1 sK2 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 sK0 X2 X0]
  have l4 : ∀ sK3 sK1 sK2 sK0 X1 X2 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro sK3 sK1 sK2 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK2 sK0 X1 X2]
  have l5 : ∀ sK3 sK1 sK2 sK0 X1 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK2 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l6 : ∀ X0 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK2 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK1 sK2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK1 sK2 sK0]
  intro x y z w u v r
  conv => enter [1]; rw [l7 x y z w u v r]

@[equational_result]
theorem Equation54683_implies_Equation4274 (G : Type*) [Magma G] (h54683 : Equation54683 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X5 : G, (X0 ◇ (sK0 ◇ sK0)) = (X5 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X5
    conv => enter [1]; rw [h54683 X0 sK0 sK0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h54683 X5 sK0 sK0 X0 X0 X0 X0]
  have l1 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h54683 X1 X2 X3 X1 X1 X1 X1]
    conv => enter [1]; rw [← h54683 X0 sK0 sK0 X1 X1 X1 X1]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l1 X0 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54411 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54411 G := by
  intro x y z
  conv => enter [1]; rw [← h4274 y x z]
  conv => enter [1]; rw [h4274 y y (y ◇ y)]

theorem Equation4512_54411_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54411 : Equation54411 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54411 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54411 X0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h54411 sK1 sK0 sK2]
    conv => enter [1]; rw [l2 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l3 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54639 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54639 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X1 X0 X2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 sK1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1]; rw [h4274 w w (w ◇ w)]

theorem Equation4512_54639_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54639 : Equation54639 G) : Equation4274 G := by
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
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54639 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l4 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l5 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l6 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54410 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54410 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4274 sK0 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4274 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l7 y x x z]
  conv => enter [1]; rw [l6 y x y]

theorem Equation4512_54410_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54410 : Equation54410 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l4 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [h54410 (sK0 ◇ sK0) sK0 (X0 ◇ X1)]
  have l6 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h54410 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54410 X0 sK0 X1]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54410 sK0 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [h54410 (sK0 ◇ sK0) sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← h54410 sK0 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 sK0]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l14 sK0 X0]
    conv => enter [1]; rw [l16 sK0 X0 sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [l20 sK0 X0 X1]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0 sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l26 sK1 sK0 sK2]
    conv => enter [1]; rw [← l25 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l27 y x z]

@[equational_result]
theorem Equation4274_implies_Equation54508 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54508 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK0]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z z x]
  conv => enter [1]; rw [l6 z x z]

theorem Equation4512_54508_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54508 : Equation54508 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l8 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← h54508 ((sK0 ◇ sK0) ◇ X0) X1 sK0]
  have l14 : ∀ sK2 X0 X1 sK0 : G, ((sK2 ◇ X0) ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h54508 (sK2 ◇ X0) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK2 X0]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54508 X0 X1 X2]
    conv => enter [1]; rw [← h54508 X0 X3 X2]
  have l16 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ X3))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← h54508 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54508 X0 X1 sK0]
  have l18 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54508 X0 X1 sK0]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l18 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l10 sK0 (sK0 ◇ X0)]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l17 sK0 X0 X1]
  have l21 : ∀ sK2 X0 X1 sK0 : G, ((sK2 ◇ X0) ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [l14 sK2 X0 X1 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))]
  have l22 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ sK0)]
  have l23 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))]
    conv => enter [1]; rw [← l19 sK0 X0 X1]
  have l24 : ∀ sK2 X0 X1 sK0 : G, ((sK2 ◇ X0) ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [l21 sK2 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l10 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0 sK0]
    conv => enter [1]; rw [← l16 sK0 (sK0 ◇ sK0) X0 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0 sK0]
    conv => enter [1]; rw [← l16 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l27 : ∀ sK2 X0 X1 sK0 : G, ((sK2 ◇ X0) ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [l24 sK2 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0))]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l25 sK0 X0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l26 sK0 X0]
  have l30 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0))) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← l27 sK2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK2 X0 (X1 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← l28 sK0 X0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← l29 sK0 X0]
  have l33 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l16 (sK0 ◇ sK0) sK2 X0 sK0]
    conv => enter [1]; rw [← l30 sK0 sK2 X0 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l31 sK0 X0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l33 sK0 sK2 X0]
    conv => enter [1]; rw [l5 sK0 ((sK0 ◇ sK0) ◇ sK2)]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0]
    conv => enter [1]; rw [l34 sK0 X0]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l35 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l39 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l36 sK0 sK2 X0]
    conv => enter [1, 2]; rw [l12 sK0 sK2]
  have l40 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)]
    conv => enter [1]; rw [← l39 sK0 sK2 X0]
  have l41 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l37 sK0 ((sK0 ◇ sK2) ◇ sK0)]
    conv => enter [1]; rw [← l40 sK0 sK2 sK0]
  have l42 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l41 sK0 sK0]
    conv => enter [1]; rw [← l38 sK0 sK0]
  have l43 : ∀ X1 sK0 X2 X0 : G, ((X1 ◇ sK0) ◇ ((X1 ◇ sK0) ◇ ((X1 ◇ sK0) ◇ X2))) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [← h54508 X2 X0 (X1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l20 sK0 X0 X1]
  have l44 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ ((X1 ◇ sK0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ sK0) X2]
    conv => enter [1, 1]; rw [← l20 sK0 X0 X1]
  have l45 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 sK0 sK0]
  have l46 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 (sK0 ◇ sK0) sK0]
  have l47 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l46 sK0]
    conv => enter [1]; rw [l8 sK0]
  have l48 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l49 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ ((X1 ◇ sK0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l44 X0 X1 sK0 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X2]
  have l50 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK0 ◇ ((X1 ◇ sK0) ◇ ((X1 ◇ sK0) ◇ X2)))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← l43 X1 sK0 X2 X0]
    conv => enter [1]; rw [← h4512 X1 sK0 ((X1 ◇ sK0) ◇ ((X1 ◇ sK0) ◇ X2))]
  have l51 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l47 sK0]
  have l52 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l48 sK0]
  have l53 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (sK0 ◇ X2))) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [← l49 X0 X1 sK0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 sK0 X2]
  have l54 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ ((X1 ◇ sK0) ◇ X2))))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [l50 X2 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 sK0 ((X1 ◇ sK0) ◇ X2)]
  have l55 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((X1 ◇ sK0) ◇ X2)))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [l54 X2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l53 sK0 sK0 ((X1 ◇ sK0) ◇ X2) X1]
  have l56 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ ((X1 ◇ sK0) ◇ X2))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [l55 X2 sK0 X0 X1]
    conv => enter [1]; rw [← l53 sK0 X1 ((X1 ◇ sK0) ◇ X2) (sK0 ◇ (sK0 ◇ sK0))]
  have l57 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ X2)))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [l56 X2 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 sK0 X2]
  have l58 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X2))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [l57 X2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l53 sK0 X1 X2 X1]
  have l59 : ∀ sK0 X2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l38 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l58 X2 sK0 X0 sK0]
  have l60 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l59 sK0 X2 X0]
  have l61 : ∀ sK0 X2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l51 sK0]
    conv => enter [1]; rw [l60 sK0 X2 X0]
  have l62 : ∀ sK0 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l52 sK0]
    conv => enter [1]; rw [l61 sK0 X2 X0]
  have l63 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l15 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l62 sK0 X0 X2]
  have l64 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l63 X0 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l64 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54636 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54636 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK2]
  have l2 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 X0]
  have l3 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 X2 X0]
  have l4 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X1 X2]
  have l5 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK1]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 sK1]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 X0 X0]
  have l8 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w x]
  conv => enter [1]; rw [l6 w x w]

theorem Equation4512_54636_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54636 : Equation54636 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ ((X3 ◇ X4) ◇ ((X3 ◇ X4) ◇ X0)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54636 X0 X1 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [← h4512 X3 X4 ((X3 ◇ X4) ◇ ((X3 ◇ X4) ◇ X0))]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54636 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ (X3 ◇ (X4 ◇ ((X3 ◇ X4) ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X3 X4 ((X3 ◇ X4) ◇ X0)]
  have l6 : ∀ X0 X1 X2 sK0 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X3) := by
    intro X0 X1 X2 sK0 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3 X0]
    conv => enter [1]; rw [l4 X3 X0 (X3 ◇ (X0 ◇ ((X3 ◇ X0) ◇ X0))) sK0]
  have l7 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l6 X1 sK0 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l7 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54413 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54413 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [← h4274 sK1 sK3 sK0]
  have l2 : ∀ sK3 sK1 sK0 X0 X1 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK3 sK1 sK0]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z y (y ◇ w)]

theorem Equation4512_54413_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54413 : Equation54413 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54413 X1 sK0 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54413 X1 sK0 sK2 X0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54413 X1 sK0 sK0 X0]
  have l3 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l1 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 X0]
  have l4 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 X2 X2]
    conv => enter [1]; rw [l2 sK0 X2 X0]
  have l5 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l4 sK1 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l5 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54509 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54509 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1 X2]
  have l5 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK0]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK0 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z z y]
  conv => enter [1]; rw [l6 z y z]

theorem Equation4512_54509_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54509 : Equation54509 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54509 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54509 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54509 (X2 ◇ X3) X1 X0]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X0)]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l7 sK0 X0]
  have l12 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK2 sK2 sK2]
    conv => enter [1]; rw [← h54509 X0 sK0 sK2]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54509 X0 sK0 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54509 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X0]
  have l17 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l12 sK0 sK2 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 X0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK0 X0]
  have l21 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [l17 sK0 sK2 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l18 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l19 X0 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l18 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l25 sK0 X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l26 sK0 X0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l27 sK0 X0]
  have l29 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l13 sK0 X0]
    conv => enter [1]; rw [l13 sK0 X1]
  have l30 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54509 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l13 sK0 X0]
  have l31 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l30 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l28 sK0 X0]
    conv => enter [1]; rw [← l31 X1 sK0 X0]
  have l33 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [l32 X0 sK0 X1]
  have l34 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54509 X1 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l18 sK0 X0]
  have l35 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l33 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l34 X1 sK0 X0]
  have l36 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [l35 X0 sK0 X1]
  have l37 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l21 sK0 sK2 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l38 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l37 sK0 sK2]
  have l39 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l36 sK0 sK0 sK2]
    conv => enter [1]; rw [← l38 sK0 sK2]
  have l40 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l21 sK0 sK2 sK1]
    conv => enter [1]; rw [← l39 sK0 sK2]
  have l41 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l40 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l42 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l41 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l36 sK0 sK0 X0]
  have l43 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l40 sK1 sK0 sK2]
    conv => enter [1]; rw [← l42 sK1 sK0 sK2 X0]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l43 sK1 sK0 sK2 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l44 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54637 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54637 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK2]
  have l2 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 X0]
  have l3 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 X2 X0]
  have l4 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X1 X2]
  have l5 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK1]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 sK1]
  have l7 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 X0 X0]
  have l8 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w y]
  conv => enter [1]; rw [l6 w y w]

theorem Equation4512_54637_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54637 : Equation54637 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ ((X3 ◇ X4) ◇ ((X3 ◇ X4) ◇ X1)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54637 X0 X1 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [← h4512 X3 X4 ((X3 ◇ X4) ◇ ((X3 ◇ X4) ◇ X1))]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54637 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ (X3 ◇ (X4 ◇ ((X3 ◇ X4) ◇ X1))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X3 X4 ((X3 ◇ X4) ◇ X1)]
  have l6 : ∀ X0 X1 X2 sK0 X4 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X4) := by
    intro X0 X1 X2 sK0 X4
    conv => enter [1]; rw [l5 X0 X1 X2 X0 X4]
    conv => enter [1]; rw [l4 X0 X4 (X0 ◇ (X4 ◇ ((X0 ◇ X4) ◇ X1))) sK0]
  have l7 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l6 X0 sK0 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l7 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54511 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54511 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK3 sK0 sK1 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK3 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK1 X1 X2]
  have l5 : ∀ sK3 sK0 sK1 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK1 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK3]
  have l6 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK3 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z z (z ◇ w)]

theorem Equation4512_54511_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54511 : Equation54511 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54511 X1 sK0 sK0 X0]
  have l1 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 X2 X2]
    conv => enter [1]; rw [l0 sK0 X2 X0]
  have l2 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4512 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 (X1 ◇ X2) sK0 X0]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l2 X1 X2 sK0 sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 X1 sK0]
  have l5 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54511 X1 X2 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l1 X0 sK0 sK0]
  have l6 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l5 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l7 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l6 X1 X2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54640 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54640 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK4 sK1 sK0 X1 X2 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK4 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK1 sK0 X1 X2]
  have l5 : ∀ sK4 sK1 sK0 X1 X0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK4]
  have l6 : ∀ X0 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK4 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK1 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK4 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w w (w ◇ u)]

@[equational_result]
theorem Equation54640_implies_Equation4274 (G : Type*) [Magma G] (h54640 : Equation54640 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 X5 X6 X7 : G, (X0 ◇ (X1 ◇ X2)) = (X5 ◇ (X6 ◇ X7)) := by
    intro X0 X1 X2 X5 X6 X7
    conv => enter [1]; rw [h54640 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54640 X5 X6 X7 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54407 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54407 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 sK2]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 sK0 sK1 sK2]
  have l2 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [h4274 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y z y (x ◇ y)]

theorem Equation4512_54407_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54407 : Equation54407 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54407 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54407 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0]
  have l11 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
    conv => enter [1]; rw [l9 sK0 sK2]
  have l12 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l11 sK0 sK2]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54407 X0 sK0 X1]
  have l14 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l11 sK0 sK2]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l15 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54624 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54624 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK1)]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK2 ◇ sK1)]
  have l2 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK2 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK2 X0]
  have l3 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 X2 X0]
  have l4 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X1 X2]
  have l5 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w x]

theorem Equation4512_54624_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54624 : Equation54624 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ X1 X4 X5 X2 X3 X0 : G, (X1 ◇ (X4 ◇ X5)) = ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X4 X5 X2 X3 X0
    conv => enter [1]; rw [h54624 X1 X4 X5 (X2 ◇ X3)]
    conv => enter [1, 2, 2]; rw [h54624 X1 X2 X3 X0]
  have l3 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (X1 ◇ X2)) = (((sK0 ◇ sK0) ◇ X0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h54624 sK0 X1 X2 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54624 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54624 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l3 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l8 : ∀ X1 X4 X5 X2 X3 X0 : G, (X1 ◇ (X4 ◇ X5)) = (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X1 X4 X5 X2 X3 X0
    conv => enter [1]; rw [l2 X1 X4 X5 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X2 X3 ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))]
  have l9 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l6 sK0 sK0 (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 X1 X2 sK0]
  have l10 : ∀ X1 X4 X5 sK0 X2 : G, (X1 ◇ (X4 ◇ X5)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X4 X5 sK0 X2
    conv => enter [1]; rw [l8 X1 X4 X5 X2 X1 X1]
    conv => enter [1]; rw [l5 X2 X1 ((X2 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) sK0]
  have l11 : ∀ sK0 X1 X4 X5 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X4 ◇ X5)) := by
    intro sK0 X1 X4 X5
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 X1 X4 X5 sK0 sK0]
  have l12 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l11 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l11 sK0 X0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54415 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54415 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4274 sK0 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4274 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l2 y z x z]

theorem Equation4512_54415_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54415 : Equation54415 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54415 X1 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l3 sK0 X0]
  have l6 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h54415 X0 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 sK0]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54415 (X2 ◇ X3) X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ X1)]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54415 X0 sK0 sK0]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l5 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))]
  have l10 : ∀ X1 sK0 X0 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l9 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l7 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X0 ((sK0 ◇ sK0) ◇ X0)]
  have l11 : ∀ X1 sK0 X0 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ sK0) ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l10 X1 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ sK0) (sK0 ◇ sK0) sK0]
  have l12 : ∀ X1 sK0 X0 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ sK0) ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l11 X1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ sK0) ◇ sK0)]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l12 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK0 sK0]
  have l14 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l7 sK0 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← l13 X1 sK0 X0]
  have l15 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l14 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0 X1 X0]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 X1 X0]
  have l18 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l17 sK0 X1 X0]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [l8 sK0 X1]
  have l20 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1, 2, 2]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h54415 X1 (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l20 sK0 X1 X0]
  have l22 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l19 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l23 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l22 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l19 X0 sK0 sK0]
  have l24 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l23 sK0 sK0 X1]
  have l25 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l19 X0 sK0 sK0]
  have l26 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l21 sK0 sK0 X1]
    conv => enter [1]; rw [l25 sK0 sK0 X1]
  have l27 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 X1]
  have l28 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l6 X0 sK0 sK2]
    conv => enter [1]; rw [← l6 X1 sK0 sK2]
  have l29 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l28 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK2 X0]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK0 sK2]
    conv => enter [1]; rw [l28 sK0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l30 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54419 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54419 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK1)]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4274 sK1 sK1 (sK2 ◇ sK1)]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z w
  conv => enter [1]; rw [← l2 y w x z]

theorem Equation4512_54419_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54419 : Equation54419 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54419 X1 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54419 X1 sK0 sK2 X0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54419 X1 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X0]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK0 sK0 X0]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l9 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
    conv => enter [1]; rw [l8 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l9 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54629 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54629 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK1)]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK2 ◇ sK1)]
  have l2 : ∀ X1 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK2 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK2 X0]
  have l3 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 X2 X0]
  have l4 : ∀ sK1 sK2 X1 X2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK1 sK2 X1 X2]
  have l5 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w y]

theorem Equation4512_54629_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54629 : Equation54629 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54629 X0 (sK0 ◇ sK0) X1 sK0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54629 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l4 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [← l3 X0 X0 (sK1 ◇ X0) sK0]
    conv => enter [1]; rw [← h54629 X1 sK1 (sK0 ◇ sK2) X0]
  have l5 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← l3 X0 X0 (sK0 ◇ X0) sK0]
    conv => enter [1]; rw [← h54629 X1 sK0 sK2 X0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l3 X0 X0 (sK0 ◇ X0) sK0]
    conv => enter [1]; rw [← h54629 X1 sK0 sK0 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l8 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK0 sK0 X0 sK1 sK2]
  have l9 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK0 (X0 ◇ X1) sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK2))]
  have l10 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X0 X1 sK1 sK2]
  have l11 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0]
    conv => enter [1]; rw [l8 sK0 X0 sK1 sK2]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK0 sK0 sK0]
  have l13 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l6 sK0 X0 X0]
    conv => enter [1]; rw [l6 sK0 X0 X2]
  have l14 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l5 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [← l5 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l16 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0) X0]
  have l17 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l12 sK0]
  have l18 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l14 sK1 sK0 sK2]
    conv => enter [1]; rw [← l17 sK1 sK0 sK2 X0]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l18 sK1 sK0 sK2 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54634 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54634 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 sK2]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK2]
  have l2 : ∀ X1 sK0 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 X2 X0]
  have l4 : ∀ sK3 sK0 sK2 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK3 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 X1 X2]
  have l5 : ∀ sK3 sK0 sK2 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK2 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK2) sK3]
  have l6 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK3 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w w (z ◇ w)]

theorem Equation4512_54634_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54634 : Equation54634 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ X0) ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h54634 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l6 sK0 X0]
  have l8 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ ((X3 ◇ X4) ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54634 X0 X1 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [← h4512 X3 X4 ((X3 ◇ X4) ◇ (X2 ◇ (X3 ◇ X4)))]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X2 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54634 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X2 ◇ sK0)]
  have l10 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (X2 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54634 X0 X1 X2 sK0]
  have l11 : ∀ sK0 X0 X1 X2 sK2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ sK2) ◇ (sK2 ◇ (X2 ◇ sK2))) := by
    intro sK0 X0 X1 X2 sK2
    conv => enter [1, 2]; rw [h54634 X0 X1 X2 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK2 ◇ (X2 ◇ sK2))]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54634 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (X2 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l10 sK0 X2 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X2 ◇ sK0)]
  have l14 : ∀ X0 X1 X2 X3 sK0 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ ((X2 ◇ (X3 ◇ X4)) ◇ sK0))) := by
    intro X0 X1 X2 X3 sK0 X4
    conv => enter [1]; rw [l8 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [l9 X4 (X3 ◇ X4) (X2 ◇ (X3 ◇ X4)) sK0]
  have l15 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l7 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54634 X0 X1 sK0 sK0]
  have l17 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l9 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 X0 X1 X2]
  have l18 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l14 X0 X1 X2 X3 sK0 X0]
    conv => enter [1, 2]; rw [l12 (sK0 ◇ sK0) (X2 ◇ (X3 ◇ X0)) sK0 sK0]
  have l19 : ∀ X1 X2 sK0 sK2 X0 : G, (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ (sK2 ◇ ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) ◇ sK2))) := by
    intro X1 X2 sK0 sK2 X0
    conv => enter [1]; rw [l15 X1 X2 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0 (sK0 ◇ X0) (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) sK2]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0 X0 X1]
  have l21 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X0 X1 X2]
  have l22 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l18 X0 X1 X2 X3 sK0]
    conv => enter [1, 2, 2]; rw [← l6 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ X1 X2 sK0 X0 sK2 : G, (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) ◇ sK2) ◇ sK0)) := by
    intro X1 X2 sK0 X0 sK2
    conv => enter [1]; rw [l19 X1 X2 sK0 sK2 X0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK2) sK2 ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) ◇ sK2) sK0]
  have l24 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l21 sK0 X0 X1 X2]
  have l25 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l22 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l26 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l23 X1 X2 sK0 X1 X1]
    conv => enter [1]; rw [l12 (sK0 ◇ sK0) ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) ◇ X1) sK0 sK0]
  have l27 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l25 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [l9 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l28 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l26 X1 X2 sK0]
  have l29 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l27 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK0]
  have l30 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l29 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [← l20 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l30 X0 X1 X2 X0 sK0]
    conv => enter [1]; rw [← l28 sK0 X0 sK0]
  have l32 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 sK0 sK0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l33 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [l31 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [← l35 sK0 X0]
  have l37 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l36 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← h54634 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l37 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54644 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54644 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK4 sK1 sK0 X1 X2 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK4 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK1 sK0 X1 X2]
  have l5 : ∀ sK4 sK1 sK0 X1 X0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK4]
  have l6 : ∀ X0 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK4 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK1 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK4 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w w (u ◇ w)]

@[equational_result]
theorem Equation54644_implies_Equation4274 (G : Type*) [Magma G] (h54644 : Equation54644 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 X5 X6 X7 : G, (X0 ◇ (X1 ◇ X2)) = (X5 ◇ (X6 ◇ X7)) := by
    intro X0 X1 X2 X5 X6 X7
    conv => enter [1]; rw [h54644 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54644 X5 X6 X7 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54406 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54406 G := by
  have l0 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 X1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4274 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK0 sK1 X0 X0]
  have l6 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z y x]
  conv => enter [1]; rw [l1 y x y]

theorem Equation4512_54406_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54406 : Equation54406 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54406 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54406 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54406 X0 sK0 X1]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l9 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54500 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54500 G := by
  have l0 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 X1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4274 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X1 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK0 sK1 X0 X0]
  have l6 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z z x]
  conv => enter [1]; rw [l1 z x z]

theorem Equation4512_54500_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54500 : Equation54500 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l7 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l8 sK0 sK2]
  have l14 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54500 (sK0 ◇ sK0) X0 sK0]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54500 X0 X1 X2]
    conv => enter [1]; rw [← h54500 X0 X3 X2]
  have l17 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ X3))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← h54500 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l18 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54500 X0 X1 sK0]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l18 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l10 sK0 (X0 ◇ X0)]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l7 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l21 sK0 X0 sK0]
    conv => enter [1]; rw [← l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l22 sK0 (sK0 ◇ sK0)]
  have l26 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l22 sK0 sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [← l22 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54500 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l27 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l26 sK0]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l25 sK0]
  have l31 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l30 sK0]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l31 sK0]
  have l33 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l33 sK0 X0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l29 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [← l34 sK0 X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l36 sK0 X0]
  have l38 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (X2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← h54500 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54500 sK0 sK0 X0]
  have l40 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [h54500 sK0 sK2 X0]
  have l41 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l14 sK0 sK2 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54500 sK0 X0 sK2]
  have l42 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l12 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54500 sK0 X0 (sK0 ◇ sK0)]
  have l43 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l41 sK0 sK2 X0]
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ sK2)]
  have l45 : ∀ sK0 X0 X1 X2 sK2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ sK2) ◇ X2) := by
    intro sK0 X0 X1 X2 sK2
    conv => enter [1]; rw [← l38 X2 sK0 X0 X1]
    conv => enter [1]; rw [← l40 sK0 sK2 X2]
  have l46 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l24 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l43 sK0 X0]
  have l47 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l17 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK2) sK2]
    conv => enter [1]; rw [l44 sK0 sK2 X0]
  have l48 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l46 sK0 sK0]
    conv => enter [1]; rw [l45 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0) sK2]
  have l49 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l45 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK2 sK2]
    conv => enter [1]; rw [← l47 sK0 sK0 sK2]
  have l50 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l37 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l48 sK0 sK2]
  have l51 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ sK2) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l49 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l52 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l25 sK0]
    conv => enter [1]; rw [l50 sK0 sK2]
  have l53 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l51 sK0 sK2]
    conv => enter [1]; rw [l45 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) (sK0 ◇ sK0) sK2]
  have l54 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l52 sK0 sK2]
  have l55 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [l54 sK0 sK2]
  have l56 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [l55 sK0 sK2]
  have l57 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54500 sK0 sK0 sK0]
  have l58 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l57 sK0]
  have l59 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l58 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l60 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [l16 X1 X2 (X3 ◇ X0) sK0]
    conv => enter [1, 2]; rw [h54500 sK0 X3 X0]
  have l61 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l58 sK0]
    conv => enter [1]; rw [l16 X0 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l62 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ sK2)) = (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l16 X0 X1 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l53 sK0 sK2]
  have l63 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 sK0]
    conv => enter [1]; rw [← l10 sK0 X1]
  have l64 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l16 sK0 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 X1]
  have l65 : ∀ sK1 X0 X1 sK0 sK2 : G, (sK1 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK1 X0 X1 sK0 sK2
    conv => enter [1]; rw [l16 sK1 X0 X1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) X1]
  have l66 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l63 sK0 X0 X1]
    conv => enter [1]; rw [← l59 sK0 X1]
  have l67 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l63 sK0 X0 X1]
    conv => enter [1]; rw [l64 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK2]
  have l68 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ sK2)) := by
    intro X0 sK0 X1 sK2
    conv => enter [1, 2]; rw [l56 sK0 sK2]
    conv => enter [1]; rw [← l62 X0 X1 sK2 sK0]
  have l69 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [l60 X1 X2 X3 X0 sK0]
    conv => enter [1, 2]; rw [l16 X0 X0 (sK0 ◇ sK0) sK0]
  have l70 : ∀ sK0 X1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [← l66 sK0 sK0 X1]
    conv => enter [1]; rw [l67 sK0 sK0 X1 sK2]
  have l71 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l68 X0 sK0 X0 sK2]
    conv => enter [1]; rw [l16 X0 X0 sK2 sK0]
  have l72 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [l69 X1 X2 X3 X0 sK0]
    conv => enter [1]; rw [← l61 X1 sK0 X0]
  have l73 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l61 X0 sK0 sK0]
    conv => enter [1]; rw [l71 X0 sK0 sK2]
  have l74 : ∀ X1 X0 sK0 X2 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK2))) := by
    intro X1 X0 sK0 X2 sK2
    conv => enter [1]; rw [l16 X1 X0 (sK0 ◇ (sK0 ◇ sK0)) X2]
    conv => enter [1, 2]; rw [l73 X2 sK0 sK2]
  have l75 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [l74 X1 X0 sK0 X1 sK2]
    conv => enter [1]; rw [l16 X1 X1 (sK0 ◇ sK2) sK1]
  have l76 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [l61 X1 sK0 X1]
    conv => enter [1]; rw [l75 X1 X1 sK0 sK1 sK2]
  have l77 : ∀ sK1 sK0 sK2 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1]; rw [h54500 (sK1 ◇ (sK0 ◇ sK2)) X1 X0]
    conv => enter [1, 2, 2]; rw [← l76 (sK1 ◇ (sK0 ◇ sK2)) sK0 sK1 sK2]
  have l78 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← l72 X0 X0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l77 sK1 sK0 sK2 X1 X0]
  have l79 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l39 sK0 (sK0 ◇ sK2)]
  have l80 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l65 sK1 (sK0 ◇ sK0) (sK0 ◇ sK2) sK0 sK2]
    conv => enter [1]; rw [← l79 sK1 sK0 sK2]
  have l81 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l78 (sK0 ◇ sK0) sK0 sK1 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l80 sK1 sK0 sK2]
  have l82 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l81 sK0 sK1 sK2]
    conv => enter [1]; rw [← l73 (sK1 ◇ (sK0 ◇ sK2)) sK0 sK2]
  have l83 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [l82 sK0 sK1 sK2]
  have l84 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l58 sK0]
    conv => enter [1]; rw [l83 sK0 sK1 sK2]
  have l85 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l84 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l86 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l85 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← l78 X0 sK0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l87 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l16 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l86 sK0 X0]
  have l88 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h54500 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [l86 sK0 X0]
  have l89 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l84 sK0 sK1 sK2]
    conv => enter [1]; rw [← l86 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l90 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l89 sK0 sK0 sK0]
  have l91 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l88 X0 sK0]
    conv => enter [1]; rw [l64 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l92 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l87 X1 X2 X0 sK0]
    conv => enter [1]; rw [← l61 X1 sK0 X0]
  have l93 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l70 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l91 X0 sK0 sK0]
  have l94 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l93 sK0 X0]
    conv => enter [1]; rw [l92 X0 X0 (sK0 ◇ sK0) sK0]
  have l95 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l90 sK0]
    conv => enter [1]; rw [l94 sK0 X0]
  have l96 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l95 sK0 sK1]
    conv => enter [1]; rw [l73 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l96 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54621 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54621 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4274 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h4274 sK2 X0 (sK2 ◇ sK2)]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 sK1 sK2]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4274 sK2 sK1 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 sK2]
  have l4 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 sK1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK2]
    conv => enter [1]; rw [l4 sK2 X0 sK1]
  have l6 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w x]
  conv => enter [1]; rw [l5 w x w]

theorem Equation4512_54621_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54621 : Equation54621 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54621 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54621 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X0)]
  have l7 : ∀ sK1 sK0 sK2 X0 X1 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ X0))) = (sK1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) ((sK0 ◇ sK2) ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54621 X0 X1 X2 (sK0 ◇ sK2)]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h54621 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l9 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ X1) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h54621 sK0 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK2 X1]
  have l10 : ∀ sK1 sK0 sK2 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) = (sK1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) X1]
    conv => enter [1, 2]; rw [← l9 X0 sK0 sK2 X1]
  have l11 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ X0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK0 sK2 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK1 sK0 sK2 X1 X0]
  have l12 : ∀ sK1 sK0 sK2 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [← l11 sK1 sK0 sK2 sK1 X1]
    conv => enter [1]; rw [l6 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) (sK1 ◇ sK1) sK0]
  have l13 : ∀ sK1 sK0 sK2 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l12 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0]
  have l14 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l13 sK1 sK0 sK2 X1]
  have l15 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X1]
  have l16 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X1]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54621 X0 X1 X2 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l9 sK0 sK0 X0 ((sK0 ◇ X0) ◇ (X0 ◇ X0))]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1]; rw [← l16 sK0 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 sK0]
  have l20 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l17 X0 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54421 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54421 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 X1 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4274 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK1 sK2 X0 X0]
  have l6 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l6 x y z y w]
  conv => enter [1]; rw [l1 y w y]

theorem Equation4512_54421_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54421 : Equation54421 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54421 X1 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54421 X1 sK0 sK2 X0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54421 X1 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X0]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK0 sK0 X0]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l9 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
    conv => enter [1]; rw [l8 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l9 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54505 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54505 G := by
  have l0 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4274 sK1 sK2 sK0]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l1 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK2 sK0]
  have l2 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l0 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 X0 sK2 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z z]
  conv => enter [1]; rw [l3 z y z]

theorem Equation4512_54505_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54505 : Equation54505 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54505 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54505 X1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54505 (X2 ◇ X3) X1 X0]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X0)]
  have l5 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l4 sK0 sK0 sK2 sK2]
    conv => enter [1]; rw [← h54505 X0 sK0 sK2]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54505 X0 sK0 sK0]
  have l7 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X0 sK2]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l7 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h54505 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0 sK2]
  have l12 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l9 X1 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X0 sK2]
  have l14 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l12 X1 sK0 X0]
  have l15 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK0 X1 X0]
  have l16 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54505 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l15 sK0 X1 X0]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0 X1 X0]
  have l18 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0 X1 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 X0]
  have l20 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l19 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l21 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l18 sK0 sK0 X0]
  have l23 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1]; rw [← l22 sK1 sK0 sK2 X0]
  have l24 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l23 sK1 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l25 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l24 sK1 sK0 sK2]
    conv => enter [1]; rw [l10 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l25 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54627 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54627 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4274 sK2 sK1 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 sK2]
  have l1 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 sK1 sK2]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 X0 sK1]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l3 w y x z]
  conv => enter [1]; rw [l2 w y w]

theorem Equation4512_54627_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54627 : Equation54627 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54627 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ X1)]
  have l3 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h54627 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54627 X2 sK0 sK0 X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54627 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0]
  have l5 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l3 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l5 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l3 X0 sK0 sK0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0 X1]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← h54627 X2 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l3 X1 sK0 sK0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← l8 X0 X1 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1]; rw [l2 X0 X0 (sK0 ◇ sK0) sK0]
  have l11 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h54627 X1 X0 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK0 X0]
  have l12 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l11 X1 X0 X2 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l13 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l12 X1 X0 X2 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54515 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54515 G := by
  have l0 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 X1 sK2]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4274 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK1 sK2 X0 X0]
  have l6 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l6 x y z z w]
  conv => enter [1]; rw [l1 z w z]

theorem Equation4512_54515_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54515 : Equation54515 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54515 X1 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X0]
    conv => enter [1]; rw [← l2 X1 sK0 X0]
  have l4 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l3 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l4 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l3 X0 sK0 sK0]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 sK0 X1]
  have l7 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54515 X1 X2 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l3 (sK0 ◇ sK0) sK0 sK0]
  have l8 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l7 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 X0]
  have l9 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l8 X1 X2 X0 sK0]
  have l10 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h54515 sK2 sK2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h54515 X0 sK0 sK2 sK0]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0 sK2]
  have l12 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l9 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54645 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54645 G := by
  have l0 : ∀ X0 sK3 X1 : G, (X0 ◇ (sK3 ◇ sK3)) = (X1 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3 X1
    conv => enter [1]; rw [← h4274 sK3 X0 sK3]
    conv => enter [1]; rw [h4274 sK3 X1 sK3]
  have l1 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l0 sK2 sK3 sK3]
    conv => enter [1]; rw [h4274 sK3 X0 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 sK3 sK3 sK2]
  have l2 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK3)) ◇ (sK2 ◇ (sK3 ◇ sK3))) = (X0 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1, 2]; rw [l1 sK2 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [h4274 (sK2 ◇ (sK3 ◇ sK3)) X0 X1]
  have l3 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X0 ◇ ((sK2 ◇ (sK3 ◇ sK3)) ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 (sK2 ◇ (sK3 ◇ sK3))]
    conv => enter [1]; rw [l2 sK2 sK3 X0 X1]
  have l4 : ∀ sK2 sK3 X1 X0 : G, (sK2 ◇ (sK3 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l3 sK2 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ (sK3 ◇ sK3)) sK2]
  have l5 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK2 sK3 X0 X0]
  have l6 : ∀ X1 X0 X2 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK3 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 sK2 sK3]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z w u]
  conv => enter [1]; rw [l1 w u w]

@[equational_result]
theorem Equation54645_implies_Equation4274 (G : Type*) [Magma G] (h54645 : Equation54645 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 X5 X6 X7 : G, (X0 ◇ (X1 ◇ X2)) = (X5 ◇ (X6 ◇ X7)) := by
    intro X0 X1 X2 X5 X6 X7
    conv => enter [1]; rw [h54645 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← h54645 X5 X6 X7 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54409 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54409 G := by
  have l0 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 sK3]
  have l1 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK3]
  have l2 : ∀ X1 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X1 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK3) sK2 sK3 X0]
  have l3 : ∀ X0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro X0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK2 sK3 X2 X0]
  have l4 : ∀ sK1 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK2 sK3 X1 X2]
  have l5 : ∀ sK1 sK2 sK3 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK3) sK1]
  have l6 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK3) sK2 sK3 sK1]
  have l7 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK1 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 X2 sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z y x w]
  conv => enter [1]; rw [l6 y x w y]

theorem Equation4512_54409_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54409 : Equation54409 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54409 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54409 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← l0 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l3 sK0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l4 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X1]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h54409 X0 (sK0 ◇ sK0) X2 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2]; rw [← l8 sK0]
  have l12 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h54409 X1 X0 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l11 sK0 X1]
  have l13 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l12 X1 X0 X2 sK0]
    conv => enter [1, 2]; rw [← l11 sK0 X0]
  have l14 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l13 X1 X0 X2 sK0]
    conv => enter [1]; rw [← l11 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l14 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54622 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54622 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK3)]
  have l1 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK2 ◇ sK3)]
  have l2 : ∀ X1 sK1 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X1 sK1 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK2 ◇ sK3)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK3)) sK1 sK2 sK3 X0]
  have l3 : ∀ X0 sK1 sK2 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X2)) := by
    intro X0 sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 sK3 X2 X0]
  have l4 : ∀ sK1 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X2)) := by
    intro sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK1 sK2 sK3 X1 X2]
  have l5 : ∀ sK1 sK2 sK3 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK3)) sK1]
  have l6 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X1 X0 X2 sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w x y]

theorem Equation4512_54622_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54622 : Equation54622 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ X2 X3 X4 X1 X0 : G, (X2 ◇ (X3 ◇ X4)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X4 X1 X0
    conv => enter [1]; rw [h54622 X2 X3 X4 X1]
    conv => enter [1, 2]; rw [h54622 X1 X2 X3 X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54622 sK0 X0 X1 sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54622 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54622 sK0 sK0 X0 X1]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54622 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [l8 X1 X1 (sK0 ◇ sK0) sK0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l12 : ∀ X2 X3 X4 sK0 X1 X0 : G, (X2 ◇ (X3 ◇ X4)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0))) := by
    intro X2 X3 X4 sK0 X1 X0
    conv => enter [1]; rw [l4 X2 X3 X4 X1 X0]
    conv => enter [1]; rw [l9 X1 X0 (X0 ◇ (X1 ◇ X2)) sK0]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [l6 sK0 X1 X1]
  have l14 : ∀ sK0 X2 X3 X4 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X3 ◇ X4)) := by
    intro sK0 X2 X3 X4
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 X2 X3 X4 sK0 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0 sK0]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 X1]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l19 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54503 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54503 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z z (x ◇ w)]

theorem Equation4512_54503_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54503 : Equation54503 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h54503 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54503 sK0 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h54503 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h54503 X0 X1 sK0 sK0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1, 2]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h54503 X1 X2 X0 sK0]
  have l13 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l11 sK0 sK2]
    conv => enter [1]; rw [l12 sK2 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54625 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54625 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK3 sK1 sK0 X1 X2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK3 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK0 X1 X2]
  have l5 : ∀ sK3 sK1 sK0 X1 X0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK0 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK3]
  have l6 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w w (x ◇ u)]

theorem Equation4512_54625_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54625 : Equation54625 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h54625 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [h54625 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h54625 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l3 : ∀ sK0 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X2 ◇ X3)) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [l2 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h54625 X0 X2 X3 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54418 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54418 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK3)]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 sK1 sK1 (sK2 ◇ sK3)]
  have l2 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK3]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z w
  conv => enter [1]; rw [← l2 y w x x z]

theorem Equation4512_54418_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54418 : Equation54418 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [h54418 sK0 sK0 X1 X0]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l2 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 X1 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l6 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l5 sK0 (sK2 ◇ X0)]
    conv => enter [1]; rw [l1 sK0 sK2 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l6 sK0 sK0 X0]
    conv => enter [1]; rw [← h54418 X0 sK0 X1 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54626 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54626 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK3)]
  have l1 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK2 ◇ sK3)]
  have l2 : ∀ X1 sK1 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X1 sK1 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK2 ◇ sK3)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK3)) sK1 sK2 sK3 X0]
  have l3 : ∀ X0 sK1 sK2 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X2)) := by
    intro X0 sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 sK3 X2 X0]
  have l4 : ∀ sK1 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X2)) := by
    intro sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK1 sK2 sK3 X1 X2]
  have l5 : ∀ sK1 sK2 sK3 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK3)) sK1]
  have l6 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X1 X0 X2 sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w y x]

theorem Equation4512_54626_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54626 : Equation54626 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l6 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l7 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54626 X0 X1 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [← h4512 X3 X4 ((X3 ◇ X4) ◇ (X1 ◇ X0))]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54626 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ X0)]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54626 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (X1 ◇ X0)]
  have l10 : ∀ X0 X1 X2 sK0 X4 X3 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X4 ◇ X3))) := by
    intro X0 X1 X2 sK0 X4 X3
    conv => enter [1]; rw [l7 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [l9 X3 X4 ((X3 ◇ X4) ◇ (X1 ◇ X0)) sK0]
  have l11 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l8 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [h54626 sK2 sK0 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l10 X0 X1 X2 sK0 X0 X0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ X0) sK0]
  have l13 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [l11 sK0 sK2 X0]
  have l14 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l15 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l6 sK0 sK2]
    conv => enter [1]; rw [l13 sK0 sK2 X0]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l14 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l15 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK2)]
  have l18 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l17 sK0 sK2]
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK2) sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l16 sK0 sK0 X0 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l16 (sK0 ◇ sK0) sK0 X0 sK0]
  have l21 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 sK2]
  have l22 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l16 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l23 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 sK2]
  have l24 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l22 sK1 sK0 sK2]
    conv => enter [1]; rw [← l23 sK0 X0 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l25 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54512 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54512 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 sK1]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK1]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK1]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK1) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK3 sK0 sK1 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK3 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK1 X1 X2]
  have l5 : ∀ sK3 sK0 sK1 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK1 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK3]
  have l6 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK3 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z z (w ◇ x)]

theorem Equation4512_54512_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54512 : Equation54512 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54512 X0 X1 sK0 sK0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l2 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0 sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l6 : ∀ X2 sK0 X0 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X2 sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 X0 X2]
    conv => enter [1]; rw [← l3 sK0 X2 X0 X2]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1, 2, 2]; rw [l11 sK0 X1]
    conv => enter [1]; rw [← h54512 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l11 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1))]
    conv => enter [1]; rw [← h54512 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l14 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l13 sK0 X0 X0]
    conv => enter [1]; rw [l12 X0 sK0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l14 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54631 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54631 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 sK2]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK2]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK2]
  have l2 : ∀ X1 sK0 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK0 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK2) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 X2 X0]
  have l4 : ∀ sK3 sK0 sK2 X1 X2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK3 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 X1 X2]
  have l5 : ∀ sK3 sK0 sK2 X1 X0 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK2 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK2) sK3]
  have l6 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK3 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK3 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w w (z ◇ x)]

theorem Equation4512_54631_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54631 : Equation54631 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54631 X0 X1 sK0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← h54631 X0 X1 (sK0 ◇ sK0) sK0]
  have l7 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ ((X3 ◇ X4) ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54631 X0 X1 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [← h4512 X3 X4 ((X3 ◇ X4) ◇ (X2 ◇ X0))]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54631 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X2 ◇ X0)]
  have l9 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X2 ◇ X0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (X2 ◇ X0))]
    conv => enter [1, 2]; rw [← h54631 X0 X1 X2 sK0]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54631 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (X2 ◇ X0)]
  have l11 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ X0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l9 sK0 X2 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X2 ◇ X0)]
  have l12 : ∀ X0 X1 X2 X3 sK0 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ ((X2 ◇ X0) ◇ X4))) := by
    intro X0 X1 X2 X3 sK0 X4
    conv => enter [1]; rw [l7 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [l8 X4 (X3 ◇ X4) (X2 ◇ X0) sK0]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l14 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h54631 (sK0 ◇ sK2) X0 sK1 X0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK2) X0 sK1 sK0]
  have l15 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l11 sK0 X0 X1 X2]
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ sK0)) X2 X0 sK0]
  have l16 : ∀ X0 X1 X2 X3 sK0 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X4 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 X3 sK0 X4
    conv => enter [1]; rw [l12 X0 X1 X2 X3 sK0 X4]
    conv => enter [1, 2]; rw [l10 (sK0 ◇ sK0) (X2 ◇ X0) X4 sK0]
  have l17 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l14 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) sK1 (sK0 ◇ sK2) sK0]
  have l18 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l16 X0 X1 X2 X3 sK0 X0]
    conv => enter [1, 2]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l8 (sK0 ◇ sK0) (sK0 ◇ sK2) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l17 X0 sK1 sK0 sK2]
  have l20 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l18 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [l8 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l21 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l19 sK0 X0 sK1 sK2]
  have l22 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l20 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [l8 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l23 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l21 sK0 X0 sK1 sK2]
  have l24 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l22 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l23 sK0 X0 sK1 sK2]
  have l26 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l24 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l25 sK0 X0 sK1 sK2]
  have l28 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l26 X0 X1 X2 X3 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ X0 X1 X2 sK0 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X3) := by
    intro X0 X1 X2 sK0 X3
    conv => enter [1]; rw [l28 X0 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l13 sK0 X3 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l29 X0 X1 X2 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ X0)))]
    conv => enter [1]; rw [← l27 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 X0]
  have l31 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l29 sK1 sK0 sK2 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [← l27 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK2]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54631 sK0 sK0 sK0 X0]
  have l33 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l32 sK0 sK0]
  have l34 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l31 sK1 sK0 sK2]
    conv => enter [1]; rw [← l33 sK0]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l34 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54641 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54641 G := by
  have l0 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK0]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 X0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK1 sK0 X2 X0]
  have l4 : ∀ sK4 sK1 sK0 X1 X2 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro sK4 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK1 sK0 X1 X2]
  have l5 : ∀ sK4 sK1 sK0 X1 X0 : G, (sK4 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK0) sK4]
  have l6 : ∀ X0 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK4 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK1 sK0 X0 X0]
  have l7 : ∀ X1 X0 X2 sK4 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w w (u ◇ x)]

theorem Equation4512_54641_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54641 : Equation54641 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54641 X0 X1 X2 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54641 X0 X1 X2 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h54641 X0 X1 X2 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l1 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← h54641 (sK0 ◇ sK2) X0 X0 X0 sK1]
    conv => enter [1]; rw [l3 (sK0 ◇ sK2) X0 X0 sK0 sK2]
  have l6 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK2) (sK0 ◇ sK2) sK0 sK2]
  have l7 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ sK2) sK0 sK0]
    conv => enter [1]; rw [← l6 X0 sK1 sK0 sK2]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 X0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l7 sK0 X0 sK0 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l12 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54417 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54417 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK2]
    conv => enter [1]; rw [h4274 sK1 X1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4274 sK1 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z y (z ◇ w)]

theorem Equation4512_54417_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54417 : Equation54417 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [← h54417 X1 sK1 (sK0 ◇ sK2) X0]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54417 X1 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ X0)]
    conv => enter [1]; rw [← h54417 X1 sK0 sK2 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54417 X1 sK0 sK0 X0]
  have l8 : ∀ X0 sK1 sK0 sK2 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2 X2
    conv => enter [1]; rw [← l4 sK1 sK0 sK2 X0 X0]
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X0 X2]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK2]
    conv => enter [1]; rw [l5 sK0 sK2 X0]
  have l10 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l9 sK0 sK2 X0]
  have l11 : ∀ sK0 sK2 X1 X2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X1))) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X1 X2 X0
    conv => enter [1]; rw [← h54417 X2 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK2) X1]
    conv => enter [1, 2]; rw [l10 sK0 sK2 X0]
  have l12 : ∀ X2 X0 X1 sK0 sK2 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)))) := by
    intro X2 X0 X1 sK0 sK2
    conv => enter [1]; rw [h54417 X2 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK2 X1]
  have l13 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l10 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ X1))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l13 sK0 sK2 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK2 X1 sK0 sK0]
  have l15 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 sK2 sK0]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ sK2) ◇ sK0) sK0 sK2]
  have l16 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [← l6 sK0 sK2 X0 X0]
    conv => enter [1]; rw [l6 sK0 sK2 X0 X2]
  have l17 : ∀ sK0 sK2 X1 X2 X3 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK2 ◇ X1) ◇ X2))) = (X3 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X2 X3 X0
    conv => enter [1]; rw [← h54417 X3 (sK0 ◇ sK0) (sK2 ◇ X1) X2]
    conv => enter [1, 2]; rw [l6 sK0 sK2 X1 X0]
  have l18 : ∀ X3 X0 sK0 sK2 X1 X2 : G, (X3 ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ X1) ◇ X2))) := by
    intro X3 X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [← l17 sK0 sK2 X1 X2 X3 X0]
    conv => enter [1]; rw [l3 sK0 ((sK2 ◇ X1) ◇ X2)]
  have l19 : ∀ sK0 sK2 X3 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)))) = (X3 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X3 X0
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK2 ◇ sK0) ◇ sK0) sK0 sK2]
    conv => enter [1]; rw [← l18 X3 X0 sK0 sK2 sK0 sK0]
  have l20 : ∀ sK0 sK2 X3 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X3 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X3 X0
    conv => enter [1]; rw [l15 sK0 sK2]
    conv => enter [1]; rw [l19 sK0 sK2 X3 X0]
  have l21 : ∀ X3 X1 X2 X0 sK0 sK2 : G, (X3 ◇ (X1 ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK2)))) := by
    intro X3 X1 X2 X0 sK0 sK2
    conv => enter [1]; rw [h54417 X3 X1 X2 (sK0 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l16 X2 sK0 sK2 X0]
  have l22 : ∀ X3 X1 X2 sK0 sK2 : G, (X3 ◇ (X1 ◇ X2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro X3 X1 X2 sK0 sK2
    conv => enter [1]; rw [l21 X3 X1 X2 X3 sK0 sK2]
    conv => enter [1, 2]; rw [← l20 sK0 sK2 X1 X3]
  have l23 : ∀ sK0 sK2 X3 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X3 ◇ (X1 ◇ X2)) := by
    intro sK0 sK2 X3 X1 X2
    conv => enter [1]; rw [l20 sK0 sK2 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l22 X3 X1 X2 sK0 sK2]
  have l24 : ∀ sK1 sK0 sK2 X3 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X3 ◇ (X1 ◇ X2)) := by
    intro sK1 sK0 sK2 X3 X1 X2
    conv => enter [1]; rw [l16 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l23 sK0 sK2 X3 X1 X2]
  have l25 : ∀ X1 sK0 X0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X1 sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 (sK1 ◇ (sK0 ◇ sK2)) X1]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK0 sK2 X0]
  have l26 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l24 sK1 sK0 sK2 (sK0 ◇ sK0) sK1 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l25 X1 sK0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l26 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54422 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54422 G := by
  have l0 : ∀ X0 sK2 sK3 sK4 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK2 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK3 ◇ sK4)]
  have l1 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h4274 sK2 sK2 (sK3 ◇ sK4)]
  have l2 : ∀ sK2 sK3 sK4 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK4]
    conv => enter [1]; rw [h4274 sK2 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [← l2 y w u x z]

theorem Equation4512_54422_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54422 : Equation54422 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54422 X2 sK0 (sK0 ◇ sK0) X0 X1]
  have l1 : ∀ sK0 X0 X1 X2 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 X1 X2 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54422 X2 sK0 sK2 X0 X1]
  have l2 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54422 X2 sK0 sK0 X0 X1]
  have l3 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 X0]
  have l4 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [← l2 sK0 X0 X0 X0]
    conv => enter [1]; rw [l0 sK0 X0 X0 X3]
  have l5 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l4 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l5 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54507 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54507 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK3)]
  have l1 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 (sK2 ◇ sK3)]
  have l2 : ∀ X1 sK1 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X1 sK1 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ (sK2 ◇ sK3)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK2 ◇ sK3)) sK1 sK2 sK3 X0]
  have l3 : ∀ X0 sK1 sK2 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X2)) := by
    intro X0 sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l2 X1 sK1 sK2 sK3 X2 X0]
  have l4 : ∀ sK1 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X2)) := by
    intro sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK1 sK2 sK3 X1 X2]
  have l5 : ∀ sK1 sK2 sK3 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ (sK2 ◇ sK3)) sK1]
  have l6 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X1 X0 X2 sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l7 x y z z y w]

end Semigroup5
