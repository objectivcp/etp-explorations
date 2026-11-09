import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54507_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54507 : Equation54507 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54507 X1 sK0 sK0 X0]
  have l3 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l2 sK0 X0 X0]
    conv => enter [1]; rw [l2 sK0 X0 X2]
  have l4 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0 X1]
  have l7 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l3 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l7 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l3 X0 sK0 sK0]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0 X1]
  have l10 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK2 sK2]
    conv => enter [1]; rw [← h54507 X0 sK0 sK2 sK0]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54630 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54630 G := by
  have l0 : ∀ X0 sK2 sK3 sK4 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK2 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK3 ◇ sK4)]
  have l1 : ∀ X0 sK2 sK3 sK4 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X0 sK2 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 (sK3 ◇ sK4)]
  have l2 : ∀ X1 sK2 sK3 sK4 X2 X0 : G, (X1 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X2)) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X1 sK2 sK3 sK4 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ (sK3 ◇ sK4)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ (sK3 ◇ sK4)) sK2 sK3 sK4 X0]
  have l3 : ∀ X0 sK2 sK3 sK4 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X2)) := by
    intro X0 sK2 sK3 sK4 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK3 sK4 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1]; rw [← l2 X1 sK2 sK3 sK4 X2 X0]
  have l4 : ∀ sK2 sK3 sK4 X1 X2 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X2)) := by
    intro sK2 sK3 sK4 X1 X2
    conv => enter [1]; rw [l3 sK2 sK2 sK3 sK4 X1 X2]
  have l5 : ∀ sK2 sK3 sK4 X1 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK3 sK4 X1 X0
    conv => enter [1]; rw [l4 sK2 sK3 sK4 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ (sK3 ◇ sK4)) sK2]
  have l6 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK3 sK4 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK3 sK4 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X1 X0 X2 sK2 sK3 sK4
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w y u]

theorem Equation4512_54630_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54630 : Equation54630 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54630 X0 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [← h54630 X1 sK0 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l0 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l1 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK0 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ X0 sK0 X2 X1 X3 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X2 ◇ (X1 ◇ X3)) := by
    intro X0 sK0 X2 X1 X3
    conv => enter [1, 2, 2]; rw [l0 sK0 sK0 X1]
    conv => enter [1]; rw [← h54630 X2 X1 X3 X0 (sK0 ◇ sK0)]
  have l5 : ∀ X0 sK0 X2 X1 X3 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ X3)) := by
    intro X0 sK0 X2 X1 X3
    conv => enter [1, 2]; rw [l3 sK0 X0]
    conv => enter [1]; rw [l4 X0 sK0 X2 X1 X3]
  have l6 : ∀ sK0 X2 X1 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X3)) := by
    intro sK0 X2 X1 X3
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 X2 X1 X3]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h54630 X0 sK0 sK2 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54513 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54513 G := by
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
  conv => enter [1]; rw [l7 x y z z w y]

theorem Equation4512_54513_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54513 : Equation54513 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [← h54513 X1 X0 sK0 sK2]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54513 X1 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l2 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK2 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 X1 sK0 X0]
  have l3 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l2 sK0 X0 X0 X0]
    conv => enter [1]; rw [l2 sK0 X0 X0 X2]
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
  have l7 : ∀ X0 sK0 X2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 X2
    conv => enter [1, 2, 2]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h54513 X2 (sK0 ◇ (sK0 ◇ sK0)) X0 X0]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0 sK0]
    conv => enter [1]; rw [← l7 X0 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 2, 2]; rw [l11 sK0 X1]
    conv => enter [1]; rw [← h54513 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 2]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l12 X0 sK0 X2 X1]
  have l14 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l13 X0 sK0 X2 X1]
  intro x y z
  conv => enter [1]; rw [l14 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54632 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54632 G := by
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
  conv => enter [1]; rw [l7 x y z w z y]

theorem Equation4512_54632_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54632 : Equation54632 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← h54632 X1 X0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h54632 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54632 X2 sK0 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54632 X0 sK0 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54632 X0 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [h54632 X0 sK0 sK0 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54632 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l18 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l16 X0 sK0 X1]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l15 sK0 X1]
    conv => enter [1]; rw [l18 sK0 X1 X0]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l19 sK0 X0 X1]
  have l21 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l8 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l22 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l21 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l8 X0 sK0 sK0]
  have l23 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l22 sK0 sK0 X1]
  have l24 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l25 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l20 sK0 sK0 X1]
    conv => enter [1]; rw [← l24 sK0 X1 sK0]
  have l26 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [l25 sK0 X1]
  have l27 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [l26 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h54632 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l27 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54642 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54642 G := by
  have l0 : ∀ X0 sK2 sK3 sK4 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK2 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK3 ◇ sK4)]
  have l1 : ∀ X0 sK2 sK3 sK4 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X0 sK2 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 (sK3 ◇ sK4)]
  have l2 : ∀ X1 sK2 sK3 sK4 X2 X0 : G, (X1 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X2)) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X1 sK2 sK3 sK4 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ (sK3 ◇ sK4)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ (sK3 ◇ sK4)) sK2 sK3 sK4 X0]
  have l3 : ∀ X0 sK2 sK3 sK4 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X2)) := by
    intro X0 sK2 sK3 sK4 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK3 sK4 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1]; rw [← l2 X1 sK2 sK3 sK4 X2 X0]
  have l4 : ∀ sK2 sK3 sK4 X1 X2 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X2)) := by
    intro sK2 sK3 sK4 X1 X2
    conv => enter [1]; rw [l3 sK2 sK2 sK3 sK4 X1 X2]
  have l5 : ∀ sK2 sK3 sK4 X1 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK3 sK4 X1 X0
    conv => enter [1]; rw [l4 sK2 sK3 sK4 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ (sK3 ◇ sK4)) sK2]
  have l6 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK3 sK4 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK3 sK4 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X1 X0 X2 sK2 sK3 sK4
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u y]

theorem Equation4512_54642_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54642 : Equation54642 G) : Equation4274 G := by
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
  have l3 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h54642 X1 X0 X2 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l3 X1 X0 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) sK0 X0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l4 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l6 sK0 sK0]
  have l8 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l4 X0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l7 sK1 sK0 sK2]
  have l9 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0 sK1 sK2]
  have l10 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
    conv => enter [1]; rw [l9 sK0 X0 sK1 sK2]
  have l11 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l10 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK2))]
  have l12 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l11 sK1 sK0 sK2 sK1 X1]
    conv => enter [1]; rw [l4 sK1 X1 (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l13 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54516 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54516 G := by
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
  have l4 : ∀ sK1 sK0 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK1 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 X1 X2]
  have l5 : ∀ sK1 sK0 sK2 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK2) sK1]
  have l6 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z z z (w ◇ u)]

theorem Equation4512_54516_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54516 : Equation54516 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54516 X1 X2 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54516 X2 sK0 sK0 X0 X1]
  have l4 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [← l3 sK0 X0 X0 X0]
    conv => enter [1]; rw [l3 sK0 X0 X0 X3]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54516 X0 X1 X2 sK0 sK0]
    conv => enter [1, 2]; rw [l4 X2 sK0 sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l7 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l6 sK0 X2]
  have l9 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l2 sK2 sK2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h54516 X0 sK0 sK2 sK0 sK0]
  have l10 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X0 sK2]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l10 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54635 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54635 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 sK3]
  have l1 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 sK3]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 sK3]
  have l2 : ∀ X1 sK0 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) = ((sK0 ◇ sK3) ◇ (X0 ◇ (sK0 ◇ sK3))) := by
    intro X1 sK0 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 X0]
  have l3 : ∀ X0 sK0 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro X0 sK0 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 (sK0 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 X2 X0]
  have l4 : ∀ sK1 sK0 sK3 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro sK1 sK0 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK3 X1 X2]
  have l5 : ∀ sK1 sK0 sK3 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK3) sK1]
  have l6 : ∀ X0 sK1 sK0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK1 sK0 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro X1 X0 X2 sK1 sK0 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w w (z ◇ u)]

theorem Equation4512_54635_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54635 : Equation54635 G) : Equation4274 G := by
  have l0 : ∀ X3 X4 X2 X1 X0 sK0 : G, (X3 ◇ (X4 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X3 X4 X2 X1 X0 sK0
    conv => enter [1]; rw [h54635 X3 X4 X2 X1 sK0]
    conv => enter [1, 2]; rw [h54635 X1 X2 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54635 sK0 sK0 sK0 X0 sK0]
  have l2 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h54635 sK1 (sK0 ◇ sK2) sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l4 : ∀ X3 X4 X2 X1 sK1 sK0 sK2 : G, (X3 ◇ (X4 ◇ X2)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK0)) := by
    intro X3 X4 X2 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l0 X3 X4 X2 X1 X3 sK0]
    conv => enter [1, 2]; rw [l2 X3 sK0 sK1 sK2]
  have l5 : ∀ sK0 X3 X4 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X3 ◇ (X4 ◇ X2)) := by
    intro sK0 X3 X4 X2
    conv => enter [1]; rw [← h54635 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 X3 X4 X2 sK0 sK0 sK0 sK0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l6 sK0 X1 sK0]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X1]
  have l9 : ∀ sK0 X2 X3 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X3 ◇ X0)) := by
    intro sK0 X2 X3 X0
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h54635 X2 X3 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54646 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54646 G := by
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
  intro x y z w u v
  conv => enter [1]; rw [l7 x y z w w (u ◇ v)]

@[equational_result]
theorem Equation54646_implies_Equation4274 (G : Type*) [Magma G] (h54646 : Equation54646 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 X6 X7 X8 : G, (X0 ◇ (X1 ◇ X2)) = (X6 ◇ (X7 ◇ X8)) := by
    intro X0 X1 X2 X6 X7 X8
    conv => enter [1]; rw [h54646 X0 X1 X2 X0 X0 X0]
    conv => enter [1]; rw [← h54646 X6 X7 X8 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x x x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54394 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54394 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK1 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4274 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 sK1 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 sK1]
  have l3 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l2 x y y]

theorem Equation4512_54394_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54394 : Equation54394 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l7 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l8 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [h54394 (sK0 ◇ sK0) sK0 (X0 ◇ X1)]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [← l10 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l12 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l13 sK0 X0 X1]
  have l15 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l14 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [l15 sK0 sK0 sK0 X2]
  have l17 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 sK2 X0]
  have l18 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l17 sK0 sK2 X0]
    conv => enter [1]; rw [h54394 sK0 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l19 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK2 X0]
  have l21 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 sK0 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l22 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [← l24 sK0 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l27 : ∀ sK0 X1 sK2 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 X1 sK2 X0
    conv => enter [1]; rw [← h54394 X1 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54394 sK0 sK0 X0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h54394 (sK0 ◇ sK0) sK0 X0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54394 X0 sK0 X1]
    conv => enter [1]; rw [← h54394 X0 sK0 sK0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l35 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ ((sK0 ◇ sK2) ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [← l27 sK0 X1 sK2 X0]
    conv => enter [1]; rw [← h54394 X1 sK0 sK0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l26 sK0 sK0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l3 sK0]
  have l38 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l0 sK0 sK2 X0]
    conv => enter [1]; rw [l37 sK0 (sK2 ◇ X0)]
  have l39 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
    conv => enter [1]; rw [l37 sK0 sK2]
  have l40 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l38 sK0 sK2 X0]
    conv => enter [1]; rw [← l39 sK0 sK2]
  have l41 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l35 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [l40 sK0 sK2 sK0]
  have l42 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l41 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l35 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [← l42 sK0 X0 sK0]
  have l44 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l43 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← h54394 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l44 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l36 sK0 sK0]
  have l46 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1]; rw [l32 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l47 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l46 sK0 X0]
    conv => enter [1]; rw [← l32 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l47 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54561 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54561 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK2 sK1]
  have l3 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK2 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK2 sK1]
  have l5 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 sK2]
  have l6 : ∀ X1 X0 X2 sK2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z x w]
  conv => enter [1]; rw [l5 x w w]

theorem Equation4512_54561_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54561 : Equation54561 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54561 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ (X0 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54561 X0 X1 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [← h4512 X3 X4 (X0 ◇ ((X3 ◇ X4) ◇ (X3 ◇ X4)))]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (X4 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l3 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X4 (X3 ◇ X4)]
  have l5 : ∀ X0 X1 X2 sK0 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0 X3
    conv => enter [1]; rw [l4 X0 X1 X2 X3 X0]
    conv => enter [1]; rw [l2 X3 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) sK0]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0 X0]
    conv => enter [1]; rw [h54561 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l6 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l7 X0 X1 X2 sK0]
    conv => enter [1]; rw [l1 sK0]
  have l9 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l8 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54428 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54428 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK1 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4274 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 sK1 sK0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 sK1]
  have l3 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4274 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l3 z y x]
  conv => enter [1]; rw [l2 z y y]

theorem Equation4512_54428_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54428 : Equation54428 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54428 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54428 X1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54428 X0 sK0 sK0]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54428 X0 sK0 sK2]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54428 (X2 ◇ X3) X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ X1)]
  have l5 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l6 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h54428 (sK0 ◇ sK2) sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK2 X0]
  have l7 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X1 X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l9 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 X0 sK2]
  have l10 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54428 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X1 X0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X1 X0]
  have l12 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X1 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 X0]
  have l14 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l14 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l12 sK0 sK0 X0]
  have l17 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l14 sK1 sK0 sK2]
    conv => enter [1]; rw [← l16 sK1 sK0 sK2 X0]
  have l18 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l17 sK1 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l19 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l18 sK1 sK0 sK2]
    conv => enter [1]; rw [l8 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l19 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54446 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54446 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK2 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK2 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l0 sK2 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X0 sK2]
  have l3 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK1]
    conv => enter [1]; rw [h4274 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l3 w y x z]
  conv => enter [1]; rw [l2 w y y]

theorem Equation4512_54446_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54446 : Equation54446 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h54446 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54446 X2 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54446 X0 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54446 (X0 ◇ X1) sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l6 : ∀ X2 sK0 X3 X1 X0 : G, (X2 ◇ ((sK0 ◇ sK0) ◇ X3)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 sK0 X3 X1 X0
    conv => enter [1]; rw [h54446 X2 (sK0 ◇ sK0) X3 X1]
    conv => enter [1, 2, 2]; rw [l2 (sK0 ◇ sK0) sK0 X0]
  have l7 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l2 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l7 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l2 X0 sK0 sK0]
  have l9 : ∀ sK0 X2 X3 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X2 ◇ ((sK0 ◇ sK0) ◇ X3)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [← l6 X2 sK0 X3 sK0 sK0]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0 X1]
  have l11 : ∀ sK0 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK0 ◇ sK0) ◇ X3)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X2 X3]
  have l12 : ∀ sK0 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK0 ◇ sK0) ◇ X3)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l11 sK0 X2 X3]
  have l13 : ∀ sK0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ ((sK0 ◇ sK0) ◇ X3)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X2 X3]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l2 X0 sK0 sK0]
  have l15 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 sK0 X1]
    conv => enter [1]; rw [l14 sK0 sK0 X1]
  have l16 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h54446 X1 X0 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l15 sK0 (X0 ◇ X0)]
  have l17 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l16 X1 X0 X2 sK0]
    conv => enter [1]; rw [← l10 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l17 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54587 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54587 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK2 sK1]
  have l3 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK2 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK2 sK1]
  have l5 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 sK2]
  have l6 : ∀ X1 X0 X2 sK2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z y w]
  conv => enter [1]; rw [l5 y w w]

theorem Equation4512_54587_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54587 : Equation54587 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54587 X0 sK0 X1 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l6 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54613 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54613 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK2 sK1]
  have l3 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK2 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK2 sK1]
  have l5 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 sK2]
  have l6 : ∀ X1 X0 X2 sK2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z z w]
  conv => enter [1]; rw [l5 z w w]

theorem Equation4512_54613_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54613 : Equation54613 G) : Equation4274 G := by
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
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54613 X0 X1 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54613 X0 X1 (sK0 ◇ sK0) sK0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54613 X0 X1 sK0 sK0]
  have l10 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54613 X0 X1 sK2 sK0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 X0 X1]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [h54613 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l15 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l19 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l23 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54613 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l22 sK0]
  have l24 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l23 X1 X2 X0 sK0]
    conv => enter [1]; rw [h54613 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l25 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l15 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l24 X1 X2 X0 sK0]
  have l26 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l25 sK0 X1 X2 X0]
  have l27 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l10 sK0 sK2 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 sK2 X0 sK0]
  have l28 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l27 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l29 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l28 sK1 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1 sK1 (sK0 ◇ sK2)]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54613 sK0 sK0 X0 sK0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 sK0 X0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1]; rw [← l19 sK0]
  have l33 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l29 sK1 sK0 sK2]
    conv => enter [1]; rw [← l32 sK0 X0]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l33 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l34 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54668 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54668 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4274 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h4274 sK2 X0 (sK2 ◇ sK2)]
  have l2 : ∀ X0 sK3 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK3 sK2
    conv => enter [1]; rw [l1 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 sK3 sK2]
  have l3 : ∀ sK3 sK2 X0 : G, (sK3 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← h4274 sK2 sK3 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 sK2]
  have l4 : ∀ sK2 X0 sK3 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK3
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 sK3 sK2]
  have l5 : ∀ sK3 sK2 X0 : G, (sK3 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [l3 sK3 sK2 sK2]
    conv => enter [1]; rw [l4 sK2 X0 sK3]
  have l6 : ∀ X1 X0 X2 sK3 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK3 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK3 sK2]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z u w]
  conv => enter [1]; rw [l5 u w w]

theorem Equation4512_54668_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54668 : Equation54668 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h54668 X0 X1 X2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l1 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54668 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (sK1 ◇ sK1)]
  have l2 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [← l1 sK1 sK1 (sK1 ◇ sK1) sK1 sK0 sK2]
    conv => enter [1]; rw [← h54668 X2 sK0 sK2 sK1 sK1]
  have l3 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [← l1 sK1 sK1 (sK1 ◇ sK1) sK1 sK0 sK2]
    conv => enter [1]; rw [← h54668 X2 sK0 sK0 sK1 sK1]
  have l4 : ∀ X2 sK0 sK2 : G, (X2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X2 sK0 sK2
    conv => enter [1]; rw [← l2 X2 sK0 sK2 X2]
    conv => enter [1]; rw [l0 (X2 ◇ (sK0 ◇ sK2)) X2 X2 sK0 sK2]
  have l5 : ∀ X2 sK0 sK2 : G, (X2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X2 sK0 sK2
    conv => enter [1]; rw [← l3 X2 sK0 sK2 X2]
    conv => enter [1]; rw [l0 (X2 ◇ (sK0 ◇ sK2)) X2 X2 sK0 sK2]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2]
    conv => enter [1]; rw [← l5 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l6 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54393 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54393 G := by
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
  have l4 : ∀ sK1 sK0 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK1 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 X1 X2]
  have l5 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 sK0 sK1 sK2]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 sK1]
  have l7 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK0 sK2]
    conv => enter [1]; rw [h4274 sK0 X0 X1]
  have l8 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [l7 sK1 sK0 sK2 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_54393_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54393 : Equation54393 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [h54393 (sK0 ◇ sK0) sK0 (X0 ◇ X1)]
  have l13 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1, 2]; rw [l7 sK0]
  have l16 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l16 sK0 X0 X1]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 sK1 (sK0 ◇ sK2)]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0]
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
  have l20 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l21 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 sK1 (sK0 ◇ sK2)]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 sK0 sK0]
    conv => enter [1]; rw [← l22 sK0 X0 sK0 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l26 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 sK2 X0]
  have l28 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l27 sK0 sK2 X0]
    conv => enter [1]; rw [h54393 sK0 sK0 ((sK0 ◇ sK2) ◇ X0)]
  have l29 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l29 sK0 sK2 X0]
  have l31 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 sK0 sK0]
  have l32 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [← l26 sK0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l32 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l33 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l24 sK0 X0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [← l35 sK0 X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ X0)]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l38 sK0 X0]
  have l40 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54393 X0 X1 X2]
    conv => enter [1]; rw [← h54393 X0 X1 X3]
  have l41 : ∀ X1 X3 X0 X2 : G, (X1 ◇ (X3 ◇ (X1 ◇ X3))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X3 X0 X2
    conv => enter [1]; rw [← h54393 X3 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54393 X0 X1 X2]
  have l42 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h54393 X1 (sK0 ◇ sK0) (sK0 ◇ X0)]
  have l43 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l39 sK0 X0]
    conv => enter [1]; rw [h54393 X0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l44 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [h54393 sK0 sK2 X0]
  have l45 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h54393 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l46 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54393 sK0 sK0 X0]
  have l47 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [h54393 sK0 X0 X1]
  have l48 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK2 ◇ (X0 ◇ sK2)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [h54393 sK2 X0 X1]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54393 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l50 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1]; rw [h54393 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l51 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l48 sK0 sK2 X0 X1]
    conv => enter [1]; rw [h54393 sK0 X0 (sK2 ◇ (X0 ◇ sK2))]
  have l52 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l47 sK0 X0 X1]
    conv => enter [1]; rw [h54393 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (X0 ◇ sK0))]
  have l53 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l46 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l54 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l44 sK0 sK2 X0]
    conv => enter [1]; rw [h54393 sK2 sK0 (sK2 ◇ sK0)]
  have l55 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l42 X1 sK0 X0]
    conv => enter [1]; rw [← l43 X1 sK0]
  have l56 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l51 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← l50 sK0 X0]
  have l57 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l52 sK0 X0 X1]
    conv => enter [1, 2]; rw [l17 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l58 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l53 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l59 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l54 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l60 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l57 sK0 X0 X1]
    conv => enter [1]; rw [l55 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l61 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l58 sK0 X0]
    conv => enter [1]; rw [← l5 sK0]
  have l62 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l59 sK0 sK2 X0]
    conv => enter [1]; rw [l56 sK0 sK2 sK0 sK2]
  have l63 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l60 sK0 X0 sK0]
  have l64 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l61 sK0 sK0]
  have l65 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
    conv => enter [1]; rw [l61 sK0 sK2]
  have l66 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l62 sK0 sK2 X0]
  have l67 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l66 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l63 sK0 sK1]
  have l68 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l67 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l65 sK0 sK2]
  have l69 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l64 sK0]
    conv => enter [1]; rw [← l65 sK0 sK2]
  have l70 : ∀ sK0 sK2 X0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK2 X0 sK1 X1
    conv => enter [1]; rw [← l68 sK1 sK0 sK2 (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0))]
    conv => enter [1]; rw [← h54393 X0 (sK1 ◇ (sK0 ◇ sK2)) X1]
  have l71 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l70 sK0 sK2 X0 sK0 sK0]
    conv => enter [1, 2]; rw [l68 sK0 sK0 sK2 sK0]
  have l72 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l71 sK0 sK0 X0]
  have l73 : ∀ sK0 X0 sK2 X1 : G, ((sK0 ◇ X0) ◇ (sK2 ◇ X1)) = (sK2 ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK2 X1
    conv => enter [1]; rw [h54393 (sK0 ◇ X0) sK2 X1]
    conv => enter [1, 2, 2]; rw [l45 sK2 sK0 X0]
  have l74 : ∀ sK0 X0 sK2 X1 : G, ((sK0 ◇ X0) ◇ (sK2 ◇ X1)) = ((sK0 ◇ sK2) ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ sK2))) := by
    intro sK0 X0 sK2 X1
    conv => enter [1]; rw [l73 sK0 X0 sK2 X1]
    conv => enter [1]; rw [← l41 (sK0 ◇ sK2) sK2 (sK0 ◇ X0) (sK0 ◇ sK2)]
  have l75 : ∀ sK0 X0 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ X0) ◇ (sK2 ◇ X1)) := by
    intro sK0 X0 sK2 X1
    conv => enter [1]; rw [← l56 sK0 sK2 sK2 ((sK0 ◇ sK2) ◇ sK2)]
    conv => enter [1]; rw [← l74 sK0 X0 sK2 X1]
  have l76 : ∀ sK0 X0 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK0 X0 sK2 X1
    conv => enter [1]; rw [l75 sK0 X0 sK2 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK2 ◇ X1)]
  have l77 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l65 sK0 sK2]
    conv => enter [1]; rw [l76 sK0 X0 sK2 X1]
  have l78 : ∀ sK0 X0 sK2 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK0 X0 sK2 X1
    conv => enter [1]; rw [l69 sK0 sK2]
    conv => enter [1]; rw [l77 sK0 sK2 X0 X1]
  have l79 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l78 sK0 X0 X0 X0]
    conv => enter [1]; rw [l40 X0 sK0 (X0 ◇ (X0 ◇ X0)) X1]
  have l80 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l79 X0 sK0 X0]
    conv => enter [1]; rw [l40 X0 sK0 X0 sK2]
  have l81 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l72 sK0 X0]
    conv => enter [1]; rw [l80 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l81 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54474 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54474 G := by
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
  have l4 : ∀ sK1 sK0 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK1 X1 X2]
  have l5 : ∀ sK1 sK0 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK1]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK1]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z x z]
  conv => enter [1]; rw [l6 x z z]

theorem Equation4512_54474_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54474 : Equation54474 G) : Equation4274 G := by
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
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l8 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l8 sK0 sK2]
  have l12 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l13 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ sK0)) = (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54474 ((sK0 ◇ sK0) ◇ X0) X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK2 X0 X1 sK0 : G, ((sK2 ◇ X0) ◇ (X1 ◇ sK0)) = (sK0 ◇ ((sK2 ◇ X0) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h54474 (sK2 ◇ X0) X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK2 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54474 sK0 X0 (sK0 ◇ sK0)]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54474 X0 X1 X2]
    conv => enter [1]; rw [← h54474 X0 X3 X2]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54474 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l18 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X2 ◇ X3))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← h54474 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54474 sK0 X0 sK0]
  have l20 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h54474 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l15 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54474 (sK0 ◇ sK0) X0 sK0]
  have l25 : ∀ sK2 X0 X1 sK0 : G, ((sK2 ◇ X0) ◇ (X1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [l14 sK2 X0 X1 sK0]
    conv => enter [1]; rw [← l18 X0 sK0 (sK2 ◇ X0) (sK0 ◇ sK2)]
  have l26 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ (X1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← l18 X0 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l22 sK0 X0]
  have l29 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) = (sK2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← l25 sK2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK2 X0 (X1 ◇ sK0)]
  have l30 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l26 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (X1 ◇ sK0)]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 X0]
  have l32 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [← l29 X0 sK0 sK2 sK0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l30 X0 sK0 sK0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l31 sK0 X0]
  have l35 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l32 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l27 sK0 X0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1, 2]; rw [← l27 sK0 X0]
  have l37 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l35 sK0 sK2 X0]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l36 sK0 X0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l38 sK0 X0]
  have l40 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l39 sK0 sK0]
    conv => enter [1]; rw [← l37 sK0 sK2 sK0]
  have l41 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l40 sK0 sK2]
  have l42 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l24 sK0 (sK0 ◇ sK0)]
  have l43 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l5 sK0 sK0]
    conv => enter [1]; rw [← l24 sK0 (sK0 ◇ sK0)]
  have l44 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l43 sK0]
  have l45 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0]
    conv => enter [1]; rw [← l42 sK0]
  have l46 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l41 sK0 sK2]
    conv => enter [1]; rw [← l20 sK2 sK0 sK0]
  have l47 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l46 sK0 sK2]
  have l48 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [l47 sK0 sK2]
  have l49 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l48 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l50 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l49 sK0 sK2]
  have l51 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [l50 sK0 sK2]
  have l52 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l51 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK0)]
  have l53 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l37 sK0 sK2 sK1]
    conv => enter [1]; rw [l52 sK1 sK0 sK2]
  have l54 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK2]
    conv => enter [1]; rw [l53 sK0 sK2 sK1]
  have l55 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l54 sK0 sK1 sK2]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
  have l57 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ (X2 ◇ sK0))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1, 2]; rw [← l20 sK2 X2 sK0]
    conv => enter [1]; rw [l16 X0 sK2 (X2 ◇ sK0) X1]
  have l58 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 X0 (sK0 ◇ sK0) sK0 X1]
  have l59 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l16 (sK0 ◇ sK0) X0 X1 sK2]
    conv => enter [1]; rw [l3 sK0 sK2 X1]
  have l60 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l16 sK0 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 X1]
  have l61 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l62 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 (sK0 ◇ sK0) X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X1]
  have l63 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l16 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 sK2]
    conv => enter [1]; rw [l12 sK0 sK2 X1]
  have l64 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l59 sK0 X0 X1 sK2]
    conv => enter [1]; rw [l60 sK0 (sK0 ◇ sK2) X1 sK2]
  have l65 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1, 2]; rw [l58 X1 sK0 X0]
    conv => enter [1]; rw [← l57 X0 sK0 sK2 X1 X0]
  have l66 : ∀ sK0 X1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [← l61 sK0 sK0 X1]
    conv => enter [1]; rw [l64 sK0 sK0 X1 sK2]
  have l67 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l65 X0 X1 sK0 sK2]
    conv => enter [1]; rw [l16 X0 (sK0 ◇ sK2) (sK0 ◇ sK2) sK1]
  have l68 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ X0))]
    conv => enter [1, 2]; rw [← l56 sK0 X0 X0]
  have l69 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l68 X0 X1 sK0]
    conv => enter [1]; rw [l67 X0 sK0 sK0 sK1 sK2]
  have l70 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l16 X0 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l69 X0 X0 sK0 sK1 sK2]
  have l71 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l27 sK0 sK0]
  have l72 : ∀ X0 sK0 X1 : G, ((X0 ◇ sK0) ◇ (X1 ◇ sK0)) = (sK0 ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54474 (X0 ◇ sK0) X1 sK0]
    conv => enter [1, 2, 2]; rw [← l27 sK0 X0]
  have l73 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← l60 sK0 (X0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK2]
    conv => enter [1]; rw [← l72 X0 sK0 X1]
  have l74 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l71 sK0]
  have l75 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l73 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 (X1 ◇ sK0)]
  have l76 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← l75 sK0 sK2 X0 X0]
  have l77 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l66 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [← l76 X0 sK0 sK0]
  have l78 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l77 sK0 X0]
    conv => enter [1]; rw [l67 X0 sK0 sK0 sK1 sK2]
  have l79 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l78 sK0 X0 sK1 sK2]
  have l80 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l79 sK0 X0 sK1 sK2]
  have l81 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l74 sK0]
    conv => enter [1]; rw [l80 sK0 X0 sK1 sK2]
  have l82 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l81 sK0 X0 sK0 sK0]
  have l83 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l82 sK0 X0]
    conv => enter [1]; rw [h54474 X0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l84 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l83 X0 sK0]
    conv => enter [1]; rw [l63 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK2]
  have l85 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l62 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← l84 X0 sK0 sK0]
  have l86 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l82 sK0 X0]
    conv => enter [1]; rw [← l85 sK0 X0]
  have l87 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l86 sK0 X0]
    conv => enter [1]; rw [l60 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK2]
  have l88 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l87 sK0 sK0 X0]
    conv => enter [1]; rw [← l66 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK0]
  have l89 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l88 sK0 X0]
    conv => enter [1]; rw [l63 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK2]
  have l90 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l89 sK0 sK0 X0]
    conv => enter [1]; rw [l62 sK0 (sK0 ◇ sK0) X0]
  have l91 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l90 sK0 X0]
    conv => enter [1]; rw [l60 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK2]
  have l92 : ∀ X0 sK0 X2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 2]; rw [l91 sK0 X0 X1]
    conv => enter [1]; rw [l16 X0 (sK0 ◇ X0) X1 X2]
  have l93 : ∀ sK0 X0 X2 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X2 ◇ X1)) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [l82 sK0 X0]
    conv => enter [1]; rw [l92 X0 sK0 X2 X1]
  intro x y z
  conv => enter [1]; rw [l93 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54558 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54558 G := by
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
  have l4 : ∀ sK2 sK1 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK2 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK2 X1 X2]
  have l5 : ∀ sK2 sK1 X1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK2]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 sK2]
  have l7 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l8 x y z x w]
  conv => enter [1]; rw [l6 x w w]

theorem Equation4512_54558_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54558 : Equation54558 G) : Equation4274 G := by
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
  have l3 : ∀ X0 X1 X2 X4 X5 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X4 ◇ X5)) := by
    intro X0 X1 X2 X4 X5
    conv => enter [1]; rw [h54558 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54558 X0 X4 X5 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54558 sK0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54558 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l5 sK0 X0 X1]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54558 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l10 sK0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l3 sK0 X0 X1 sK0 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l14 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 sK0 sK0 X2]
  have l15 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l12 X0 X0 X0 sK0]
    conv => enter [1]; rw [l3 X0 X0 X0 sK0 sK2]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l14 sK0 sK0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 X0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l17 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [l15 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54448 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54448 G := by
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
  have l4 : ∀ sK2 sK1 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK2 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK2 X1 X2]
  have l5 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4274 sK1 sK2 sK2]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 sK2]
  have l7 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l5 sK2 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z w
  conv => enter [1]; rw [← l7 w y x z]
  conv => enter [1]; rw [l6 w y y]

theorem Equation4512_54448_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54448 : Equation54448 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54448 X0 sK0 X1 (sK0 ◇ sK0)]
  have l1 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54492 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54492 G := by
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
  have l4 : ∀ sK1 sK0 X1 X2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK1 X1 X2]
  have l5 : ∀ sK1 sK0 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK1]
  have l6 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK1]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z y z]
  conv => enter [1]; rw [l6 y z z]

theorem Equation4512_54492_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54492 : Equation54492 G) : Equation4274 G := by
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
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54492 X0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54492 X0 (sK0 ◇ sK0) sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h54492 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54492 X0 sK0 sK0]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54492 (X2 ◇ X3) X1 X0]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X0)]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK2 sK2 sK0]
    conv => enter [1]; rw [← h54492 X0 sK0 sK2]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l13 sK0 sK2 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0 X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l16 sK0 sK2 (X0 ◇ X1)]
  have l22 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← l16 sK0 sK2 sK1]
    conv => enter [1]; rw [← l21 X0 X1 sK0 sK2]
  have l23 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l16 sK0 sK2 sK1]
    conv => enter [1]; rw [l16 sK0 sK2 X0]
  have l24 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l16 sK0 sK2 sK1]
  have l25 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [← l16 sK0 sK2 sK1]
    conv => enter [1]; rw [h54492 X0 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l16 sK0 sK2 sK1]
  have l26 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [← l16 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK2) X0]
  have l27 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l25 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l26 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2))]
  have l28 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l16 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l24 sK1 sK0 sK2]
  have l29 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l27 sK1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l28 sK0 sK2 sK1]
  have l30 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l23 sK1 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l29 sK1 sK0 sK2]
  have l31 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l23 (sK0 ◇ sK0) sK0 sK2 sK1]
  have l32 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l22 sK1 sK0 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l31 sK0 sK2 sK1]
  have l33 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54492 X0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l32 sK1 sK0 sK2]
  have l34 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l32 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l35 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l34 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l33 X0 sK1 sK0 sK2]
  have l36 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l10 sK0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l35 sK1 sK0 sK2 X0]
  have l37 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l30 sK1 sK0 sK2]
    conv => enter [1]; rw [← l36 X0 sK0 sK1 sK2]
  have l38 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l37 sK1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0]
  have l40 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54492 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l10 sK0 X0]
  have l41 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l42 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l41 sK0 X0 X1]
  have l43 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l40 X1 sK0 X0]
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l44 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l42 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l43 X1 sK0 X0]
  have l45 : ∀ sK1 sK0 sK2 X1 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1]; rw [l38 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l44 X0 sK0 X1]
  have l46 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 1]; rw [← l18 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X1]
  have l47 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l18 sK0 (sK0 ◇ sK2)]
  have l48 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l47 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l49 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 X1]
    conv => enter [1]; rw [← l46 X0 sK0 X1]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l15 sK1 sK0]
    conv => enter [1]; rw [← l48 sK1 sK0 sK2]
  have l51 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l49 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l52 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l50 sK0 sK0 sK0]
  have l53 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l45 sK1 sK0 sK2 sK1 X1]
    conv => enter [1]; rw [← l51 sK0 X1 sK1]
  have l54 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l52 sK0]
    conv => enter [1, 2]; rw [← l20 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l55 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l54 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l56 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l53 sK1 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l55 sK0]
  have l57 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l56 sK1 sK0 sK2]
    conv => enter [1]; rw [← l39 sK0 (sK0 ◇ sK0)]
  have l58 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l57 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l59 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l53 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l58 sK1 sK0 sK2 X0]
  have l60 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l59 sK1 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l18 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l61 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l60 sK1 sK0 sK2]
    conv => enter [1]; rw [l18 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l61 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54585 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54585 G := by
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
  have l4 : ∀ sK2 sK1 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK2 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK2 X1 X2]
  have l5 : ∀ sK2 sK1 X1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK2]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 sK2]
  have l7 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK2 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l8 x y z y w]
  conv => enter [1]; rw [l6 y w w]

theorem Equation4512_54585_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54585 : Equation54585 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54585 X0 sK0 X1 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l6 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54530 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54530 G := by
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
  conv => enter [1]; rw [l7 x y z z w (z ◇ w)]

theorem Equation4512_54530_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54530 : Equation54530 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ X1 X2 sK0 sK2 X0 : G, (X1 ◇ (X2 ◇ sK0)) = (sK0 ◇ ((sK2 ◇ X0) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro X1 X2 sK0 sK2 X0
    conv => enter [1]; rw [h54530 X1 X2 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK2 X0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54530 X0 X1 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54530 X0 X1 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h54530 X0 X1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54530 X0 X1 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ X1 X2 sK0 sK2 X0 : G, (X1 ◇ (X2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro X1 X2 sK0 sK2 X0
    conv => enter [1]; rw [l5 X1 X2 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 ((sK0 ◇ sK2) ◇ X0)]
  have l13 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 sK0 sK2]
  have l14 : ∀ X1 X2 sK0 sK2 X0 : G, (X1 ◇ (X2 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro X1 X2 sK0 sK2 X0
    conv => enter [1]; rw [l12 X1 X2 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK2 (X0 ◇ ((sK0 ◇ sK2) ◇ X0))]
  have l15 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 sK2]
  have l16 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ X0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l14 sK0 sK0 sK0 sK2 X0]
    conv => enter [1]; rw [l8 sK0 sK0 sK0 sK2]
  have l17 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l15 sK0 sK2]
    conv => enter [1]; rw [← l16 sK0 sK2 X0]
  have l18 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ X0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h54530 X1 (sK0 ◇ sK2) (sK0 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l15 sK0 sK2]
  have l19 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l17 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 sK0 sK0 X1]
  have l20 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ X0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1, 2]; rw [l11 sK0 sK0 X0]
    conv => enter [1]; rw [← h54530 X1 X2 X0 sK0]
  have l21 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK0 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l23 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [l20 X0 sK0 X1 X2]
  have l24 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l23 sK0 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l24 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54669 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54669 G := by
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
  conv => enter [1]; rw [l7 x y z w u (w ◇ u)]

theorem Equation4512_54669_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54669 : Equation54669 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54669 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
  have l1 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK2 sK1 sK0 sK2]
    conv => enter [1]; rw [← l0 X0 sK0 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54396 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54396 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 sK3]
  have l1 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK3]
  have l2 : ∀ X1 sK1 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) = ((sK1 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X1 sK1 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 X0]
  have l3 : ∀ X0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro X0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 (sK1 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 X2 X0]
  have l4 : ∀ sK2 sK1 sK3 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro sK2 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK3 X1 X2]
  have l5 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [← h4274 sK1 sK2 sK3]
  have l6 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X0 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK2]
  have l7 : ∀ sK2 sK1 sK3 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK2 sK1 sK3 X0 X1
    conv => enter [1]; rw [l5 sK2 sK1 sK3]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z x w]
  conv => enter [1]; rw [l6 x y w y]

theorem Equation4512_54396_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54396 : Equation54396 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54396 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← h54396 (sK0 ◇ sK0) sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 sK0 X1]
  have l3 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l2 sK0 X1]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X1]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l5 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
    conv => enter [1]; rw [← h54396 X0 (sK0 ◇ sK0) X2 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1, 2]; rw [← l7 sK0]
  have l11 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h54396 X1 X0 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l10 sK0 X0]
  have l12 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l11 X1 X0 X2 sK0]
    conv => enter [1, 2]; rw [← l10 sK0 X1]
  have l13 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l12 X1 X0 X2 sK0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l14 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l13 sK0 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h54396 X0 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54559 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54559 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 sK3]
  have l1 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK3]
  have l2 : ∀ X1 sK1 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) = ((sK1 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X1 sK1 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 X0]
  have l3 : ∀ X0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro X0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 (sK1 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 X2 X0]
  have l4 : ∀ sK2 sK1 sK3 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro sK2 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK3 X1 X2]
  have l5 : ∀ sK2 sK1 sK3 X1 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK3) sK2]
  have l6 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X0 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK2]
  have l7 : ∀ X0 sK2 sK1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK2 sK1 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK1 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z x w y]
  conv => enter [1]; rw [l6 x w y w]

theorem Equation4512_54559_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54559 : Equation54559 G) : Equation4274 G := by
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
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X2)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h54559 X1 ((sK0 ◇ sK0) ◇ X0) X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l3 sK0 X0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54559 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54559 sK0 X0 X1 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54559 (sK0 ◇ sK0) X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l14 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [l9 X1 sK0 X0 X2]
    conv => enter [1]; rw [l12 sK0 X1 (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l15 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X2)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)]
    conv => enter [1]; rw [← l14 X1 sK0 X0 X2]
  have l16 : ∀ sK0 X1 X0 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X2))) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l15 sK0 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X2]
  have l17 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l16 sK0 X1 sK0 sK0]
    conv => enter [1]; rw [h54559 X1 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l18 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l17 sK0 X1]
    conv => enter [1]; rw [← l13 sK0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 X1]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l19 sK0 X0]
    conv => enter [1]; rw [l19 sK0 X1]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← l13 sK0 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l4 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l13 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l13 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54559 X0 sK0 sK2 sK0]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l26 sK0 sK1 sK2]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l28 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l27 sK1 sK0 sK2]
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l28 sK1 sK0 sK2]
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l29 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l30 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54477 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54477 G := by
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
  conv => enter [1]; rw [l7 x y z z x (z ◇ w)]

theorem Equation4512_54477_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54477 : Equation54477 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54477 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h54477 (sK0 ◇ (sK0 ◇ sK0)) X1 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1]; rw [h54477 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (X2 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h54477 X2 (X0 ◇ X1) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54477 X0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54477 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [h54477 X0 sK0 sK0 X1]
  have l14 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h54477 sK0 sK2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 sK0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [h54477 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h54477 X0 X1 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ X0 X1 sK0 X2 : G, ((X0 ◇ (X1 ◇ sK0)) ◇ X2) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 sK0 X2
    conv => enter [1, 1]; rw [h54477 X0 X1 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X2]
  have l18 : ∀ X0 X1 sK0 X2 : G, ((X0 ◇ (X1 ◇ sK0)) ◇ X2) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l17 X0 X1 sK0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1]; rw [l7 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK0 sK2]
  have l22 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [← l12 sK0 X2]
    conv => enter [1]; rw [l11 sK0 X2 X0 X1]
  have l23 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ ((X1 ◇ sK0) ◇ X2)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ sK0) X2]
    conv => enter [1]; rw [l18 X0 X1 sK0 X2]
  have l24 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l19 sK0 X0 X1]
  have l25 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l26 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0 sK2]
  have l27 : ∀ sK0 X0 X2 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X2))) = (X0 ◇ (X1 ◇ (sK0 ◇ X2))) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [← l23 X0 X1 sK0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 sK0 X2]
  have l28 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l24 sK0 sK0 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l25 sK0]
  have l30 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h54477 X0 X1 (sK0 ◇ sK2) sK0]
    conv => enter [1, 2, 2]; rw [← l26 sK0 sK2]
  have l31 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l30 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← l27 sK0 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l32 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l31 X0 X1 sK0 sK2]
    conv => enter [1, 2, 2]; rw [← l29 sK0]
  have l33 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l32 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l33 X0 X1 sK0 sK2]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK2)]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l29 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [← l28 sK0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l37 sK0 X0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l40 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54477 (sK0 ◇ sK0) sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l40 sK0]
  have l42 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54477 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l41 sK0]
  have l43 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h54477 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l44 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l43 sK0 X0]
    conv => enter [1]; rw [← l39 sK0 X0]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h54477 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l44 sK0 X0]
  have l46 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54477 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l42 sK0]
  have l47 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l45 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l46 X0 X1 sK0]
  have l48 : ∀ X0 X2 X1 sK0 sK2 : G, (X0 ◇ (X2 ◇ X1)) = (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X2 X1 sK0 sK2
    conv => enter [1]; rw [h54477 X0 X2 X1 sK0]
    conv => enter [1, 2]; rw [h54477 X0 X1 sK0 sK2]
  have l49 : ∀ X0 X2 X1 sK0 sK2 : G, (X0 ◇ (X2 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X2 X1 sK0 sK2
    conv => enter [1]; rw [l48 X0 X2 X1 sK0 sK2]
    conv => enter [1, 2]; rw [l34 sK0 X0 sK0 sK2]
  have l50 : ∀ sK0 X0 X2 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X2 ◇ X1)) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [l47 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l49 X0 X2 X1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l50 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54562 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54562 G := by
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
  conv => enter [1]; rw [l7 x y z w x (w ◇ u)]

theorem Equation4512_54562_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54562 : Equation54562 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X1 X2 X3 sK0 sK2 X0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro X1 X2 X3 sK0 sK2 X0
    conv => enter [1]; rw [h54562 X1 X2 X3 sK0 (sK2 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK2 X0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54562 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l2 X1 X2 X3 sK0 X1 X1]
    conv => enter [1]; rw [l3 sK0 X1 ((sK0 ◇ X1) ◇ X1) sK0]
  have l5 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l4 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l5 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l6 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54445 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54445 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 sK3]
  have l1 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK3]
  have l2 : ∀ X1 sK1 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) = ((sK1 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X1 sK1 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 X0]
  have l3 : ∀ X0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro X0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 (sK1 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 X2 X0]
  have l4 : ∀ sK2 sK1 sK3 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro sK2 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK3 X1 X2]
  have l5 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [← h4274 sK1 sK2 sK3]
  have l6 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X0 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK2]
  have l7 : ∀ sK2 sK1 sK3 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK2 sK1 sK3 X0 X1
    conv => enter [1]; rw [l5 sK2 sK1 sK3]
    conv => enter [1]; rw [h4274 sK1 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w x]
  conv => enter [1]; rw [l6 w y x y]

theorem Equation4512_54445_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54445 : Equation54445 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54445 X0 sK0 X1 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54445 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54445 sK0 (sK0 ◇ sK0) X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l3 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 X2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK0 X0]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l5 sK0 sK0 X1]
  have l10 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [l6 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54584 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54584 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 sK3]
  have l1 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 sK3]
    conv => enter [1]; rw [h4274 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 X0 sK3]
  have l2 : ∀ X1 sK1 sK3 X2 X0 : G, (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) = ((sK1 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro X1 sK1 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK1 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 X0]
  have l3 : ∀ X0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro X0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK1 sK3 (sK1 ◇ sK3)]
    conv => enter [1]; rw [← l2 X1 sK1 sK3 X2 X0]
  have l4 : ∀ sK2 sK1 sK3 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ ((sK1 ◇ sK3) ◇ X2)) := by
    intro sK2 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK1 sK3 X1 X2]
  have l5 : ∀ sK2 sK1 sK3 X1 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK3) sK2]
  have l6 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK1 sK3 X0 (sK1 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK2]
  have l7 : ∀ X0 sK2 sK1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK2 sK1 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK1 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK2 sK1 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK1 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l8 x y z y w x]
  conv => enter [1]; rw [l6 y w x w]

theorem Equation4512_54584_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54584 : Equation54584 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54584 X0 sK0 X1 sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 sK0 X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l4 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l2 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l6 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l12 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l13 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l12 sK1 sK0 sK2]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54527 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54527 G := by
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
  conv => enter [1]; rw [l7 x y z z w (z ◇ x)]

end Semigroup5
