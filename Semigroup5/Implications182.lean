import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation4274_implies_Equation54593 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54593 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [h4274 sK0 sK3 sK0]
  have l3 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK3 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [h4274 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 sK3 sK0]
  have l5 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l3 sK3 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0 sK3]
  have l6 : ∀ X1 X0 X2 sK3 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK3 sK0]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z y u]
  conv => enter [1]; rw [l5 y u w]

theorem Equation4512_54593_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54593 : Equation54593 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ X1)) = (X2 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h54593 X0 sK0 X1 X2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l0 X0 sK0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54594 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54594 G := by
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
  have l4 : ∀ sK4 sK0 sK1 X1 X2 : G, (sK4 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK4 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK4 sK0 sK1 X1 X2]
  have l5 : ∀ sK4 sK0 sK1 X1 X0 : G, (sK4 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK4 sK0 sK1 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK4]
  have l6 : ∀ sK4 sK0 sK1 X0 : G, (sK4 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK4 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK0 sK1 X0
    conv => enter [1]; rw [l4 sK4 sK0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK4]
  have l7 : ∀ X0 sK4 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK4 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK0 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK4 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK4 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK4 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l8 x y z y u v]
  conv => enter [1]; rw [l6 y u v w]

theorem Equation4512_54594_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54594 : Equation54594 G) : Equation4274 G := by
  have l0 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 X0 X2
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54594 X2 sK0 sK0 X1 sK0 X0]
  have l1 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54594 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54594 X4 sK0 sK0 X0 X0 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l0 sK0 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54594 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54595 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54595 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK3 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK3 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK3 sK1]
  have l3 : ∀ sK3 sK1 X0 : G, (sK3 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK3 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l4 : ∀ sK1 X0 sK3 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK3
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK3 sK1]
  have l5 : ∀ sK3 sK1 X0 : G, (sK3 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK1))) := by
    intro sK3 sK1 X0
    conv => enter [1]; rw [l3 sK3 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 sK3]
  have l6 : ∀ X1 X0 X2 sK3 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK3 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z z x]
  conv => enter [1]; rw [l5 z x w]

theorem Equation4512_54595_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54595 : Equation54595 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l3 sK0 sK2]
  have l5 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54595 sK0 X0 sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54595 X0 X1 sK0 sK0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l8 sK0 X0 X0]
    conv => enter [1]; rw [l8 sK0 X0 X2]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 X0]
  have l11 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l8 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK2 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l13 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h54595 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l15 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l13 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← l12 sK0 X1]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 X0 X1 sK0]
  have l17 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l9 X0 sK0 sK2]
    conv => enter [1]; rw [l5 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l17 sK0 X0 sK2]
    conv => enter [1, 2]; rw [l11 (sK0 ◇ sK2) sK0 sK2]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l18 sK0 X0 sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l19 sK0 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ sK0) sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l22 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54595 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l24 sK0 (X2 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l25 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54596 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54596 G := by
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
  have l4 : ∀ sK3 sK1 sK2 X1 X2 : G, (sK3 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X2)) := by
    intro sK3 sK1 sK2 X1 X2
    conv => enter [1]; rw [l3 sK3 sK1 sK2 X1 X2]
  have l5 : ∀ sK3 sK1 sK2 X1 X0 : G, (sK3 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK3 sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK2 X1 (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK1 ◇ sK2) sK3]
  have l6 : ∀ sK3 sK1 sK2 X0 : G, (sK3 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK2) sK1 sK2 sK3]
  have l7 : ∀ X0 sK3 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK3 sK1 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK2 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK1 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK3 sK1 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l8 x y z z x y]
  conv => enter [1]; rw [l6 z x y w]

theorem Equation4512_54596_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54596 : Equation54596 G) : Equation4274 G := by
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
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l6 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1]; rw [← h54596 X0 X1 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l8 sK0 X0 sK0]
  have l11 : ∀ sK0 X0 X1 X2 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ sK0) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ sK0) X2]
  have l12 : ∀ sK0 X0 X1 X2 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (sK0 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l11 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 sK0 X2]
  have l13 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l9 sK0]
  have l14 : ∀ sK0 X0 X1 X2 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) ◇ X2) = (sK0 ◇ (X2 ◇ X1)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l12 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h54596 sK0 X2 X1 X0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l16 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = (sK0 ◇ (X2 ◇ X1)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ X1) X2]
    conv => enter [1]; rw [l14 sK0 X0 X1 X2]
  have l17 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (X2 ◇ X1)) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l16 sK0 X0 X1 X2]
  have l18 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (X2 ◇ X1)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [← l17 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h54596 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [← l8 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0) X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l18 (sK0 ◇ sK0) X0 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 X0 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l19 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0)]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [← l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← l15 sK0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l30 sK0 X0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l28 sK0 X0]
    conv => enter [1]; rw [l31 sK0 X0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l32 sK0 X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l33 sK0 X0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l36 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (X0 ◇ X1))) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X2 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← h54596 X0 X1 X2 (sK0 ◇ sK0)]
  have l37 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l36 sK0 X2 X0 X1]
    conv => enter [1]; rw [← h54596 X1 X2 X0 sK0]
  have l38 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [← l28 sK0 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l37 sK0 X2 X0 X1]
  have l39 : ∀ sK0 X1 X2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [l38 sK0 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l39 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54598 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54598 G := by
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
  have l6 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK1 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK0) sK1 sK0 sK3]
  have l7 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK3 sK1 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro X1 X0 X2 sK3 sK1 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z z x w]
  conv => enter [1]; rw [l6 z x w w]

theorem Equation4512_54598_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54598 : Equation54598 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54598 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54598 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [h54598 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [h54598 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1]; rw [l1 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l7 sK0 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54598 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK0 (X2 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [← l10 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54599 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54599 G := by
  have l0 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK0]
    conv => enter [1]; rw [h4274 sK2 X1 sK0]
  have l1 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK0]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK0]
  have l2 : ∀ X1 sK2 sK0 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK0) ◇ X2)) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X1 sK2 sK0 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK0) sK2 sK0 X0]
  have l3 : ∀ X0 sK2 sK0 X1 X2 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ ((sK2 ◇ sK0) ◇ X2)) := by
    intro X0 sK2 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l2 X1 sK2 sK0 X2 X0]
  have l4 : ∀ sK4 sK2 sK0 X1 X2 : G, (sK4 ◇ (sK2 ◇ sK0)) = (X1 ◇ ((sK2 ◇ sK0) ◇ X2)) := by
    intro sK4 sK2 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK2 sK0 X1 X2]
  have l5 : ∀ sK4 sK2 sK0 X1 X0 : G, (sK4 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK2 sK0 X1 X0
    conv => enter [1]; rw [l4 sK4 sK2 sK0 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK2 ◇ sK0) sK4]
  have l6 : ∀ sK4 sK2 sK0 X0 : G, (sK4 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK4 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK2 sK0 X0
    conv => enter [1]; rw [l4 sK4 sK2 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK0) sK2 sK0 sK4]
  have l7 : ∀ X0 sK4 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK4 sK2 sK0
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK2 sK0 X0 X0]
  have l8 : ∀ X1 X0 X2 sK4 sK2 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK2 ◇ sK0)) := by
    intro X1 X0 X2 sK4 sK2 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK4 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z z x u]
  conv => enter [1]; rw [l6 z x u w]

theorem Equation4512_54599_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54599 : Equation54599 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK2) ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X1]
    conv => enter [1]; rw [h54599 sK0 sK2 X1 X0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54599 sK0 X0 (sK0 ◇ sK0) sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h54599 sK0 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54599 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK2 sK0 sK0]
  have l8 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK2) ◇ X1) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [← l2 sK0 sK2 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l12 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK2) ◇ X0) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 sK2]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54599 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l14 sK0 (X2 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l15 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54600 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54600 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK3)]
  have l1 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 sK3]
  have l2 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK3]
  have l3 : ∀ X1 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X1 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK3) sK2 sK3 X0]
  have l4 : ∀ X0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro X0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l2 X0 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l3 X1 sK2 sK3 X2 X0]
  have l5 : ∀ sK1 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X1 X2]
  have l6 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 sK2 sK1 sK3]
  have l7 : ∀ X0 sK2 sK3 X1 sK1 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ X1)) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1 sK1
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK3) sK2 sK3 sK1]
  have l8 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK1 sK1]
  have l9 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK3]
    conv => enter [1]; rw [l0 (sK2 ◇ sK3) sK1 sK2 sK3 X0]
  have l10 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 sK3]
    conv => enter [1]; rw [h4274 sK2 X0 X1]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK3 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l10 sK1 sK2 sK3 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_54600_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54600 : Equation54600 G) : Equation4274 G := by
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
  have l5 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l6 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1]; rw [← h54600 X1 X0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 1]; rw [l3 sK0 X0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [← h54600 X1 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l13 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← l12 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l14 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l13 X1 X0 sK0]
    conv => enter [1]; rw [← h54600 X1 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ X1 X0 sK0 X2 : G, (X1 ◇ ((X0 ◇ sK0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X0 sK0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ sK0) X2]
    conv => enter [1, 1]; rw [← l8 sK0 X0 X1]
  have l17 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l8 sK0 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ sK0)]
  have l18 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l17 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h54600 sK0 X0 X2 X1]
  have l19 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ ((X0 ◇ sK0) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ X1) X2]
    conv => enter [1]; rw [← l16 X1 X0 sK0 X2]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l15 X0 sK0]
    conv => enter [1]; rw [l14 X0 sK0 sK0]
  have l21 : ∀ sK0 X0 X2 X1 : G, (sK0 ◇ (X0 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [← l18 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h54600 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ (sK0 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l19 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X2]
  have l23 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l22 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h54600 X2 sK0 X0 X1]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l20 sK0 X0]
    conv => enter [1]; rw [← l21 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [← l23 sK0 X0 X2 X2]
    conv => enter [1]; rw [← l21 sK0 X2 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ X2)]
  have l26 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l24 X0 sK0]
    conv => enter [1]; rw [l14 sK0 X0 sK0]
  have l27 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [l25 X2 sK0 X0]
    conv => enter [1]; rw [l14 sK0 X2 sK0]
  have l28 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [l27 X2 sK0 X0]
    conv => enter [1]; rw [← l26 X2 sK0]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l8 sK0 sK0 X0]
  have l30 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l31 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l30 sK0 X0 X1]
    conv => enter [1]; rw [← l21 sK0 X1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ X0)]
  have l32 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l31 X0 sK0 X1]
    conv => enter [1]; rw [l14 sK0 X1 sK0]
  have l33 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l26 X1 sK0]
    conv => enter [1]; rw [← l32 X0 sK0 X1]
  have l34 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l28 X1 sK0 sK0]
    conv => enter [1]; rw [l33 X1 sK0 X0]
  have l35 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 1]; rw [l28 X0 sK0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l36 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l35 X0 sK0 X1]
  have l37 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l34 X1 sK0 X0]
    conv => enter [1]; rw [l36 X0 sK0 X1]
  have l38 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54600 X0 (sK0 ◇ sK0) sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l39 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ (X1 ◇ X0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h54600 X0 X1 X2 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 (X2 ◇ (X1 ◇ X0))]
  have l40 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X1 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l39 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X0) (sK0 ◇ sK0)]
  have l41 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l37 X0 sK0 X0]
    conv => enter [1]; rw [← l38 X0 sK0 X0]
  have l42 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l40 sK0 X0 X1 X2]
    conv => enter [1]; rw [← l21 sK0 (sK0 ◇ sK0) X2 (X1 ◇ X0)]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 sK0 X0]
    conv => enter [1]; rw [← l41 X0 sK0]
  have l44 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l42 sK0 X0 X1 X2]
    conv => enter [1]; rw [← l34 X2 sK0 sK0]
  have l45 : ∀ X2 X1 X0 sK0 : G, (X2 ◇ (X1 ◇ X0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X2 X1 X0 sK0
    conv => enter [1]; rw [h54600 X2 X1 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l44 sK0 X0 X1 X2]
  have l46 : ∀ sK0 X2 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [l43 sK0 X2]
    conv => enter [1]; rw [← l45 X2 X1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l46 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54601 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54601 G := by
  have l0 : ∀ sK3 sK2 X0 : G, (sK3 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← h4274 sK2 sK3 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 sK2]
  have l1 : ∀ sK2 X0 sK3 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK3
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 sK3 sK2]
  have l2 : ∀ sK3 sK2 X0 : G, (sK3 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [l0 sK3 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 X0 sK3]
  have l3 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK3 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 sK2 sK1 sK3]
    conv => enter [1]; rw [l0 sK2 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l2 z y w]

theorem Equation4512_54601_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54601 : Equation54601 G) : Equation4274 G := by
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
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54601 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ X1)]
  have l6 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h54601 X0 sK0 sK2 X1]
    conv => enter [1, 2]; rw [l5 sK2 sK0 sK0]
  have l7 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l6 X0 sK0 sK2 X1]
    conv => enter [1, 2]; rw [← l4 sK0 sK0]
  have l8 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l7 X0 sK0 sK2 X1]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l9 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l8 X0 sK0 sK2 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ X1 sK0 X2 X3 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X2 X3 X0
    conv => enter [1]; rw [h54601 X1 (sK0 ◇ sK0) X2 X3]
    conv => enter [1, 2, 2]; rw [h54601 (sK0 ◇ sK0) sK0 sK0 X0]
  have l11 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l10 X1 sK0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h54601 sK0 sK0 sK0 X1]
  have l12 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l11 X1 sK0 X2 X3]
    conv => enter [1, 2]; rw [← h54601 sK0 sK0 sK0 X2]
  have l13 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h54601 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 X1 sK0 X2 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54601 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54601 X0 sK0 sK0 sK0]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l14 sK0 X0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 sK0 X1]
    conv => enter [1]; rw [l15 sK0 sK0 X1]
  have l17 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l16 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l9 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54603 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54603 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK1 X1 (sK2 ◇ sK3)]
  have l1 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 sK3]
  have l2 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK2 X0 sK3]
    conv => enter [1]; rw [h4274 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 X0 sK3]
  have l3 : ∀ X1 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X1 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK3) X1 X2]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK3) sK2 sK3 X0]
  have l4 : ∀ X0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro X0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l2 X0 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l3 X1 sK2 sK3 X2 X0]
  have l5 : ∀ sK1 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X2)) := by
    intro sK1 sK2 sK3 X1 X2
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X1 X2]
  have l6 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4274 sK2 sK1 sK3]
  have l7 : ∀ X0 sK2 sK3 X1 sK1 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ X1)) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1 sK1
    conv => enter [1]; rw [← h4274 (sK2 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l1 (sK2 ◇ sK3) sK2 sK3 sK1]
  have l8 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK1 sK1]
  have l9 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK3]
    conv => enter [1]; rw [l0 (sK2 ◇ sK3) sK1 sK2 sK3 X0]
  have l10 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 sK3]
    conv => enter [1]; rw [h4274 sK2 X0 X1]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l10 sK1 sK2 sK3 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_54603_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54603 : Equation54603 G) : Equation4274 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54603 X1 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 X0 sK0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X0]
    conv => enter [1]; rw [← l2 X1 sK0 X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l6 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ (X3 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h54603 X1 X2 X3 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l4 X2 sK0 X0]
  have l7 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l4 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l7 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l4 X0 sK0 sK0]
  have l9 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l6 X1 X2 X3 sK0 X1]
    conv => enter [1, 2]; rw [← l5 sK0 X3 X1]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0 X1]
  have l11 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l9 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l11 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [← l12 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54604 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54604 G := by
  have l0 : ∀ X0 sK2 sK3 sK4 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK2 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK2 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [h4274 sK2 X1 (sK3 ◇ sK4)]
  have l1 : ∀ X0 sK3 sK4 X1 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK3 X0 sK4]
    conv => enter [1]; rw [h4274 sK3 X1 sK4]
  have l2 : ∀ X0 sK3 sK4 X1 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK3 sK4 X1
    conv => enter [1]; rw [← h4274 sK3 X0 sK4]
    conv => enter [1]; rw [h4274 sK3 X1 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [h4274 sK3 X0 sK4]
  have l3 : ∀ X1 sK3 sK4 X2 X0 : G, (X1 ◇ ((sK3 ◇ sK4) ◇ X2)) = ((sK3 ◇ sK4) ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro X1 sK3 sK4 X2 X0
    conv => enter [1]; rw [← h4274 (sK3 ◇ sK4) X1 X2]
    conv => enter [1, 2]; rw [l1 (sK3 ◇ sK4) sK3 sK4 X0]
  have l4 : ∀ X0 sK3 sK4 X1 X2 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ ((sK3 ◇ sK4) ◇ X2)) := by
    intro X0 sK3 sK4 X1 X2
    conv => enter [1]; rw [l2 X0 sK3 sK4 (sK3 ◇ sK4)]
    conv => enter [1]; rw [← l3 X1 sK3 sK4 X2 X0]
  have l5 : ∀ sK2 sK3 sK4 X1 X2 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X1 ◇ ((sK3 ◇ sK4) ◇ X2)) := by
    intro sK2 sK3 sK4 X1 X2
    conv => enter [1]; rw [l4 sK2 sK3 sK4 X1 X2]
  have l6 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h4274 sK3 sK2 sK4]
  have l7 : ∀ X0 sK3 sK4 X1 sK2 : G, (X0 ◇ ((sK3 ◇ sK4) ◇ X1)) = ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK3 sK4 X1 sK2
    conv => enter [1]; rw [← h4274 (sK3 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [l1 (sK3 ◇ sK4) sK3 sK4 sK2]
  have l8 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK3 ◇ sK4)) = ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l5 sK2 sK3 sK4 sK2 sK2]
    conv => enter [1]; rw [l7 sK2 sK3 sK4 sK2 sK2]
  have l9 : ∀ sK2 sK3 sK4 X0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l8 sK2 sK3 sK4]
    conv => enter [1]; rw [l0 (sK3 ◇ sK4) sK2 sK3 sK4 X0]
  have l10 : ∀ sK2 sK3 sK4 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK3 ◇ X1)) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [l6 sK2 sK3 sK4]
    conv => enter [1]; rw [h4274 sK3 X0 X1]
  have l11 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK1 ◇ (sK4 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK3 sK4 sK1]
    conv => enter [1, 2]; rw [l10 sK2 sK3 sK4 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l11 x y z w u]

theorem Equation4512_54604_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54604 : Equation54604 G) : Equation4274 G := by
  have l0 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X2 sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54604 X1 sK0 sK0 X2 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 X0 sK0 sK0 X1]
  have l2 : ∀ X1 X2 X3 X4 X0 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X3 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 X4 X0 sK0
    conv => enter [1]; rw [h54604 X1 X2 X3 X4 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 X0 sK0 X2]
  have l3 : ∀ X1 X2 X3 X4 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 X4 sK0
    conv => enter [1]; rw [l2 X1 X2 X3 X4 X1 sK0]
    conv => enter [1, 2, 2]; rw [l1 X1 sK0 sK0]
  have l4 : ∀ X1 X2 X3 X4 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X4 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 X4 sK0
    conv => enter [1]; rw [l3 X1 X2 X3 X4 sK0]
    conv => enter [1, 2]; rw [l1 X3 sK0 sK0]
  have l5 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ X3)) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [← l1 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 X1 X2 X3 sK0 sK0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [← l1 X0 sK0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l6 sK0 X1 sK0]
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l7 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54604 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54615 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54615 G := by
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
  have l4 : ∀ sK4 sK0 sK2 X1 X2 : G, (sK4 ◇ (sK0 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK4 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK4 sK0 sK2 X1 X2]
  have l5 : ∀ sK4 sK0 sK2 X1 X0 : G, (sK4 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK4 sK0 sK2 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK2) sK4]
  have l6 : ∀ sK4 sK0 sK2 X0 : G, (sK4 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK4 ◇ (sK0 ◇ sK2))) := by
    intro sK4 sK0 sK2 X0
    conv => enter [1]; rw [l4 sK4 sK0 sK2 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 sK4]
  have l7 : ∀ X0 sK4 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK4 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK0 sK2 X0 X0]
  have l8 : ∀ X1 X0 X2 sK4 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 X2 sK4 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK4 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z z u x]
  conv => enter [1]; rw [l6 z u x w]

theorem Equation4512_54615_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54615 : Equation54615 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54615 sK0 sK0 (sK0 ◇ X0) X1 sK0]
  have l3 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [← h54615 sK0 sK2 X1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 X1]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54615 sK0 X0 (sK0 ◇ sK0) sK0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54615 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK2]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l2 sK0 X0 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0) sK0 sK2]
  have l8 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK0 X0 sK0 sK2]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l9 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l7 sK0 X0 sK2]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 (sK0 ◇ X0)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54615 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l12 sK0 (X2 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l13 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54616 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54616 G := by
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
  have l4 : ∀ sK4 sK0 sK3 X1 X2 : G, (sK4 ◇ (sK0 ◇ sK3)) = (X1 ◇ ((sK0 ◇ sK3) ◇ X2)) := by
    intro sK4 sK0 sK3 X1 X2
    conv => enter [1]; rw [l3 sK4 sK0 sK3 X1 X2]
  have l5 : ∀ sK4 sK0 sK3 X1 X0 : G, (sK4 ◇ (sK0 ◇ sK3)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK0 sK3 X1 X0
    conv => enter [1]; rw [l4 sK4 sK0 sK3 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK3) sK4]
  have l6 : ∀ sK4 sK0 sK3 X0 : G, (sK4 ◇ (sK0 ◇ sK3)) = (X0 ◇ (sK4 ◇ (sK0 ◇ sK3))) := by
    intro sK4 sK0 sK3 X0
    conv => enter [1]; rw [l4 sK4 sK0 sK3 X0 (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK4]
  have l7 : ∀ X0 sK4 sK0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK4 sK0 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK0 sK3 X0 X0]
  have l8 : ∀ X1 X0 X2 sK4 sK0 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK0 ◇ sK3)) := by
    intro X1 X0 X2 sK4 sK0 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK4 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z z u y]
  conv => enter [1]; rw [l6 z u y w]

theorem Equation4512_54616_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54616 : Equation54616 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
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
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54616 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54616 X3 sK0 sK0 X0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l9 sK0 sK0 X0]
  have l11 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l9 X0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l9 X0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l9 (sK0 ◇ sK0) sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l9 (sK0 ◇ sK0) sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l17 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l11 sK0 X0 sK2]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK2) sK2]
  have l18 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l15 sK0 sK0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l16 sK0 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l17 sK0 X0 sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l18 sK0 X0 sK0]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l23 sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l26 sK0]
  have l28 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0 sK0]
  have l30 : ∀ X2 X1 sK0 X0 : G, (X2 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X2 X1 sK0 X0
    conv => enter [1, 2, 2]; rw [l24 sK0]
    conv => enter [1]; rw [← h54616 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 X2 (sK0 ◇ sK0)]
  have l31 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X2 sK0 X0 X1
    conv => enter [1, 2]; rw [l29 sK0 X1]
    conv => enter [1]; rw [l30 X2 X1 sK0 X0]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 sK0]
    conv => enter [1]; rw [l31 sK0 sK0 X0 X1]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l27 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 sK0 X0]
    conv => enter [1]; rw [← l33 sK0 X0]
  have l35 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l34 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54616 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54618 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54618 G := by
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
  have l4 : ∀ sK4 sK0 sK1 X1 X2 : G, (sK4 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK4 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK4 sK0 sK1 X1 X2]
  have l5 : ∀ sK4 sK0 sK1 X1 X0 : G, (sK4 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK4 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK4 sK0 sK1 X1 (X0 ◇ sK4)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK4]
  have l6 : ∀ sK4 sK0 sK1 X0 : G, (sK4 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK4 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK0 sK1 X0
    conv => enter [1]; rw [l4 sK4 sK0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK4]
  have l7 : ∀ X0 sK4 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK4 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK4 sK0 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK4 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK4 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK4 sK0 sK1]
  intro x y z w u
  conv => enter [1]; rw [l8 x y z z u w]
  conv => enter [1]; rw [l6 z u w w]

theorem Equation4512_54618_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54618 : Equation54618 G) : Equation4274 G := by
  have l0 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54618 X0 X1 X2 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54618 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) X2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l1 X0 X1 X2 sK0]
    conv => enter [1]; rw [h54618 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l5 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54619 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54619 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4274 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4274 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h4274 sK0 X0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 sK4 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK4 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [h4274 sK0 sK4 sK0]
  have l3 : ∀ sK4 sK0 X0 : G, (sK4 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK4 sK0 X0
    conv => enter [1]; rw [← h4274 sK0 sK4 sK0]
    conv => enter [1]; rw [h4274 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 sK4 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK4 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK4
    conv => enter [1]; rw [h4274 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 sK4 sK0]
  have l5 : ∀ sK4 sK0 X0 : G, (sK4 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK4 ◇ (sK0 ◇ sK0))) := by
    intro sK4 sK0 X0
    conv => enter [1]; rw [l3 sK4 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0 sK4]
  have l6 : ∀ X1 X0 X2 sK4 sK0 : G, (X1 ◇ (X0 ◇ X2)) = (sK4 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 X2 sK4 sK0
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK4 sK0]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z z u]
  conv => enter [1]; rw [l5 z u w]

theorem Equation4512_54619_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54619 : Equation54619 G) : Equation4274 G := by
  have l0 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l4 : ∀ X1 sK0 X0 sK2 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro X1 sK0 X0 sK2
    conv => enter [1]; rw [h54619 X1 sK0 sK0 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 sK2]
  have l5 : ∀ X0 sK0 X3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X3
    conv => enter [1]; rw [h54619 X0 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← h54619 X3 sK0 sK0 X0 X0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 sK0]
  have l9 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l4 sK0 sK0 X0 sK2]
  have l10 : ∀ X3 sK0 X4 X1 X0 sK2 : G, (X3 ◇ ((sK0 ◇ sK0) ◇ (X4 ◇ X4))) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ sK2))) := by
    intro X3 sK0 X4 X1 X0 sK2
    conv => enter [1]; rw [← h54619 X1 X3 (sK0 ◇ sK0) X3 X4]
    conv => enter [1, 2]; rw [l4 X3 sK0 X0 sK2]
  have l11 : ∀ sK0 X4 X1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X4 ◇ X4)) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ sK2))) := by
    intro sK0 X4 X1 X0 sK2
    conv => enter [1]; rw [l6 sK0 (X4 ◇ X4) sK0]
    conv => enter [1]; rw [l10 sK0 sK0 X4 X1 X0 sK2]
  have l12 : ∀ X1 sK0 X4 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X4 ◇ X4)) := by
    intro X1 sK0 X4
    conv => enter [1, 2]; rw [l9 sK0 X1 X1]
    conv => enter [1]; rw [← l11 sK0 X4 X1 X1 X1]
  have l13 : ∀ sK0 X4 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X4 ◇ X4)) := by
    intro sK0 X4
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK0 X4]
  have l14 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l13 sK0 X1]
    conv => enter [1]; rw [h54619 (sK0 ◇ (sK0 ◇ sK0)) X1 X1 X0 X2]
  have l15 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (X1 ◇ X1))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h54619 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [l3 sK0 sK2 (X1 ◇ X1)]
  have l16 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ sK0) (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l15 X0 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54620 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54620 G := by
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
  have l4 : ∀ sK5 sK0 sK1 X1 X2 : G, (sK5 ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro sK5 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK5 sK0 sK1 X1 X2]
  have l5 : ∀ sK5 sK0 sK1 X1 X0 : G, (sK5 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK5 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK5 sK0 sK1 X1 (X0 ◇ sK5)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ sK1) sK5]
  have l6 : ∀ sK5 sK0 sK1 X0 : G, (sK5 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK5 ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK0 sK1 X0
    conv => enter [1]; rw [l4 sK5 sK0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK5]
  have l7 : ∀ X0 sK5 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK5 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK5 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK5 sK0 sK1 X0 X0]
  have l8 : ∀ X1 X0 X2 sK5 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK5 ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 X2 sK5 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 sK5 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l8 x y z z u v]
  conv => enter [1]; rw [l6 z u v w]

theorem Equation4512_54620_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54620 : Equation54620 G) : Equation4274 G := by
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
  have l4 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54620 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54620 X4 sK0 sK0 X0 X0 X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0]
  have l7 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h54620 X0 sK0 sK0 (sK0 ◇ sK0) sK0 sK2]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l7 sK0 sK2 sK0]
  have l9 : ∀ X0 sK0 X1 sK2 X2 X3 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK2) ◇ (X2 ◇ X3))) := by
    intro X0 sK0 X1 sK2 X2 X3
    conv => enter [1, 2]; rw [l8 sK0 sK2]
    conv => enter [1]; rw [h54620 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK2) X1 X2 X3]
  have l10 : ∀ sK0 X1 sK2 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK2) ◇ (X2 ◇ X3))) := by
    intro sK0 X1 sK2 X2 X3
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X1 sK2 X2 X3]
  have l11 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (X1 ◇ X2))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [h54620 X0 sK0 sK2 (sK0 ◇ sK0) X1 X2]
    conv => enter [1]; rw [l3 sK0 sK2 (X1 ◇ X2)]
  have l12 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l10 sK0 sK0 sK2 sK0 sK0]
    conv => enter [1]; rw [← l11 X0 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54647 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54647 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4274 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 sK2 X0 sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 X0 sK2]
    conv => enter [1]; rw [← h4274 sK2 X0 (sK2 ◇ sK2)]
  have l2 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l1 X0 sK2]
    conv => enter [1]; rw [h4274 sK2 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4274 sK2 sK0 sK2]
    conv => enter [1]; rw [h4274 sK2 X0 sK2]
  have l4 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h4274 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4274 sK2 sK0 sK2]
  have l5 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2 sK2]
    conv => enter [1]; rw [l4 sK2 X0 sK0]
  have l6 : ∀ X1 X0 X2 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 X2 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z u x]
  conv => enter [1]; rw [l5 u x w]

theorem Equation4512_54647_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54647 : Equation54647 G) : Equation4274 G := by
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
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← h54647 sK0 (sK0 ◇ sK0) X2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X2]
  have l10 : ∀ X0 X1 sK0 sK2 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK2) ◇ X2) := by
    intro X0 X1 sK0 sK2 X2
    conv => enter [1]; rw [← h54647 sK0 sK2 X2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK2 X2]
  have l11 : ∀ sK0 X2 X3 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X2 ◇ X3)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X3 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X2 ◇ X3)]
    conv => enter [1, 2]; rw [h54647 sK0 X2 X3 X0 X1]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54647 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l13 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54647 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (X0 ◇ X0)]
  have l14 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54647 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ X0)]
  have l15 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l13 X0 X1 X2 sK1 sK0 sK2]
    conv => enter [1]; rw [l14 (sK1 ◇ (sK0 ◇ sK2)) X0 X0 sK0]
  have l16 : ∀ sK0 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X3)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [← l14 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l11 sK0 X2 X3 sK0 sK0]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l15 X0 X1 X2 sK0 X0 X0]
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ (sK0 ◇ X0)) (X0 ◇ (sK0 ◇ X0)) sK0]
  have l18 : ∀ sK0 X2 X3 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X3)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 X2 X3]
  have l19 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l17 X0 X1 X2 sK0]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l20 : ∀ sK0 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X2 ◇ X3)) := by
    intro sK0 X2 X3
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l18 sK0 X2 X3]
  have l21 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l19 X0 X1 X2 sK0]
    conv => enter [1]; rw [l12 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l22 : ∀ sK0 X2 X3 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X2 ◇ X3)) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0 X2 X3]
  have l23 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l21 X0 X1 X2 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l23 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l25 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l24 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK1 sK0 sK2 X2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) X2]
    conv => enter [1, 2]; rw [← l10 X0 X1 sK0 sK2 X2]
  have l27 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [l26 sK1 sK0 sK2 X2 sK1 sK1]
    conv => enter [1]; rw [l14 sK1 sK1 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l28 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [l27 sK1 sK0 sK2 X2]
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK1 sK0]
  have l29 : ∀ sK1 sK0 sK2 X2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X2
    conv => enter [1]; rw [l28 sK1 sK0 sK2 X2]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l30 : ∀ sK0 sK1 sK2 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [l22 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l29 sK1 sK0 sK2 X2]
  have l31 : ∀ X2 sK0 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X2 sK0 X0
    conv => enter [1]; rw [l10 X2 sK0 sK0 X2 X2]
    conv => enter [1]; rw [← l10 X0 sK0 sK0 X2 X2]
  have l32 : ∀ sK0 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) sK0 sK0 X0]
    conv => enter [1]; rw [← l10 X2 sK0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 X0]
    conv => enter [1]; rw [← l30 sK0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54647 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l25 sK0 sK0 (sK0 ◇ sK0) sK0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [l33 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [l31 (sK0 ◇ sK0) sK0 X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 sK0]
    conv => enter [1]; rw [← l32 sK0 X0 sK0]
  have l38 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54647 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l37 sK0 (X0 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l38 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54648 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54648 G := by
  have l0 : ∀ X0 sK0 sK2 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK2 ◇ sK3)]
  have l1 : ∀ X0 sK0 sK2 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK0 sK2 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK2 ◇ sK3)]
  have l2 : ∀ X1 sK0 sK2 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X2)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro X1 sK0 sK2 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK2 ◇ sK3)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK2 ◇ sK3)) sK0 sK2 sK3 X0]
  have l3 : ∀ X0 sK0 sK2 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X2)) := by
    intro X0 sK0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 sK3 (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 sK3 X2 X0]
  have l4 : ∀ sK1 sK0 sK2 sK3 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X2)) := by
    intro sK1 sK0 sK2 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK3 X1 X2]
  have l5 : ∀ sK1 sK0 sK2 sK3 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK2 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK2 ◇ sK3)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK2 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK2 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro X1 X0 X2 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK2 sK3]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u x y]

theorem Equation4512_54648_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54648 : Equation54648 G) : Equation4274 G := by
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
  have l4 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← h54648 sK0 sK0 X2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54648 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54648 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ X1)]
  have l7 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l6 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l4 X0 X1 sK0 X2]
  have l8 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l5 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0 sK0 X2]
  have l9 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 X2]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X2]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X1]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 X0]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54648 X0 X1 X2 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l12 sK0 (X0 ◇ (X0 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l13 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54650 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54650 G := by
  have l0 : ∀ X0 sK0 sK2 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK2 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK2 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK2 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK2 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK2 ◇ sK1)]
  have l2 : ∀ X1 sK0 sK2 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X2)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro X1 sK0 sK2 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK2 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK2 ◇ sK1)) sK0 sK2 sK1 X0]
  have l3 : ∀ X0 sK0 sK2 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro X0 sK0 sK2 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 sK1 X2 X0]
  have l4 : ∀ sK1 sK0 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro sK1 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK1 X1 X2]
  have l5 : ∀ sK1 sK0 sK2 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK2 ◇ sK1)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 X2 sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u x]

theorem Equation4512_54650_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54650 : Equation54650 G) : Equation4274 G := by
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
  have l5 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X4 ◇ X5)) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [← h54650 X2 X0 (X3 ◇ X2) X0 X1]
    conv => enter [1]; rw [← h54650 X3 X4 X5 X2 X0]
  have l6 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← h54650 sK0 sK0 X2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54650 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54650 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l8 X0 sK0 (sK0 ◇ X0) sK0]
    conv => enter [1]; rw [l6 X0 sK0 sK0 X2]
  have l10 : ∀ X3 X4 X5 sK0 X0 : G, (X3 ◇ (X4 ◇ X5)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X3 X4 X5 sK0 X0
    conv => enter [1]; rw [← l5 X0 X3 X3 X3 X4 X5]
    conv => enter [1]; rw [l8 X0 X3 (X3 ◇ X0) sK0]
  have l11 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l7 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X2]
  have l12 : ∀ sK0 X3 X4 X5 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X3 ◇ (X4 ◇ X5)) := by
    intro sK0 X3 X4 X5
    conv => enter [1]; rw [← l7 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l10 X3 X4 X5 sK0 sK0]
  have l13 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X2]
  have l14 : ∀ sK0 X3 X4 X5 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X3 ◇ (X4 ◇ X5)) := by
    intro sK0 X3 X4 X5
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X3 X4 X5]
  have l15 : ∀ sK0 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X2]
  have l16 : ∀ sK0 X3 X4 X5 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X3 ◇ (X4 ◇ X5)) := by
    intro sK0 X3 X4 X5
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X3 X4 X5]
  have l17 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l15 sK0 X2]
  have l18 : ∀ sK0 X3 X4 X5 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X3 ◇ (X4 ◇ X5)) := by
    intro sK0 X3 X4 X5
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l16 sK0 X3 X4 X5]
  have l19 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l17 sK0 X2]
  have l20 : ∀ sK0 X3 X4 X5 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X3 ◇ (X4 ◇ X5)) := by
    intro sK0 X3 X4 X5
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 X3 X4 X5]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l19 sK0 X0]
    conv => enter [1]; rw [l19 sK0 X1]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l23 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0 X0 sK0 sK2]
  have l26 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l25 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l26 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54651 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54651 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK2 ◇ sK0)]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK2 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK0 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK2 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK2 ◇ sK0)) sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK0 sK2 X2 X0]
  have l4 : ∀ sK1 sK0 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro sK1 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 X1 X2]
  have l5 : ∀ sK1 sK0 sK2 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK2 ◇ sK0)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 X2 sK1 sK0 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u x]

theorem Equation4512_54651_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54651 : Equation54651 G) : Equation4274 G := by
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
  have l5 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X1 ◇ (sK0 ◇ X1))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X2]
    conv => enter [1]; rw [h54651 sK0 sK0 X2 X0 X1]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54651 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54651 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ sK0)]
  have l8 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ X2) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l5 sK0 X2 X0 sK0]
    conv => enter [1]; rw [l7 X0 sK0 (sK0 ◇ sK0) sK0]
  have l9 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l6 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 X2 sK0]
  have l10 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X2]
  have l11 : ∀ sK0 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X2]
  have l12 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l11 sK0 X2]
  have l13 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l12 sK0 X2]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l13 sK0 X0]
    conv => enter [1]; rw [l13 sK0 X1]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK0 X0]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54651 X0 X1 X2 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l16 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54652 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54652 G := by
  have l0 : ∀ X0 sK0 sK3 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro X0 sK0 sK3 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK3 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK3 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro X0 sK0 sK3 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK3 ◇ sK1)]
  have l2 : ∀ X1 sK0 sK3 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ X2)) = ((sK0 ◇ (sK3 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro X1 sK0 sK3 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK3 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK3 ◇ sK1)) sK0 sK3 sK1 X0]
  have l3 : ∀ X0 sK0 sK3 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ X2)) := by
    intro X0 sK0 sK3 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 sK1 (sK0 ◇ (sK3 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK3 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ X2)) := by
    intro sK2 sK0 sK3 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK3 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK3 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK3 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK3 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK3 ◇ sK1)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK3 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro X0 sK2 sK0 sK3 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK3 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK3 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro X1 X0 X2 sK2 sK0 sK3 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK3 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l7 x y z w u x v]

@[equational_result]
theorem Equation54652_implies_Equation4274 (G : Type*) [Magma G] (h54652 : Equation54652 G) : Equation4274 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 sK0 sK2 : G, (X2 ◇ (X3 ◇ X4)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro X2 X3 X4 X0 X1 sK0 sK2
    conv => enter [1]; rw [h54652 X2 X3 X4 sK0 X2 X2]
    conv => enter [1]; rw [h54652 sK0 X2 (X2 ◇ X2) X0 X1 sK2]
  have l1 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h54652 sK0 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [h54652 sK0 sK0 (sK0 ◇ sK0) X0 X1 sK2]
  have l2 : ∀ sK0 X2 X3 X4 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X3 ◇ X4)) := by
    intro sK0 X2 X3 X4
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X2 X3 X4 sK0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y x z]

@[equational_result]
theorem Equation4274_implies_Equation54653 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54653 G := by
  have l0 : ∀ X0 sK0 sK3 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro X0 sK0 sK3 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK3 ◇ sK2)]
  have l1 : ∀ X0 sK0 sK3 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro X0 sK0 sK3 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK3 ◇ sK2)]
  have l2 : ∀ X1 sK0 sK3 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK3 ◇ sK2)) ◇ X2)) = ((sK0 ◇ (sK3 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK2)))) := by
    intro X1 sK0 sK3 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK3 ◇ sK2)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK3 ◇ sK2)) sK0 sK3 sK2 X0]
  have l3 : ∀ X0 sK0 sK3 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK2)) ◇ X2)) := by
    intro X0 sK0 sK3 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 sK2 (sK0 ◇ (sK3 ◇ sK2))]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 sK2 X2 X0]
  have l4 : ∀ sK1 sK0 sK3 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK2)) ◇ X2)) := by
    intro sK1 sK0 sK3 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK3 sK2 X1 X2]
  have l5 : ∀ sK1 sK0 sK3 sK2 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK3 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK3 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK3 ◇ sK2)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK3 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro X0 sK1 sK0 sK3 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK3 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK3 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK2))) := by
    intro X1 X0 X2 sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK3 sK2]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u y x]

theorem Equation4512_54653_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54653 : Equation54653 G) : Equation4274 G := by
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
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ X0 X1 sK0 sK2 sK1 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK2) ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) := by
    intro X0 X1 sK0 sK2 sK1 X2
    conv => enter [1]; rw [← h54653 sK1 (sK0 ◇ sK2) X2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) X2]
  have l7 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54653 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ X0)]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54653 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ X0)]
  have l9 : ∀ sK1 sK0 sK2 X2 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK1 sK0 sK2 X2 X1 X0
    conv => enter [1]; rw [← l6 X0 X1 sK0 sK2 sK1 X2]
    conv => enter [1]; rw [l8 X0 X1 ((sK0 ◇ sK2) ◇ sK1) sK0]
  have l10 : ∀ sK1 sK0 sK2 X2 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X2 X1
    conv => enter [1]; rw [l9 sK1 sK0 sK2 X2 X1 sK1]
    conv => enter [1]; rw [l7 (sK0 ◇ (sK0 ◇ sK0)) X1 sK1 sK0]
  have l11 : ∀ sK1 sK0 sK2 X2 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X2 X1
    conv => enter [1]; rw [l10 sK1 sK0 sK2 X2 X1]
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l12 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK0 sK2 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l5 sK0]
  have l13 : ∀ X1 X2 X3 X4 sK0 X0 : G, (X1 ◇ (X2 ◇ X3)) = (X4 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 X4 sK0 X0
    conv => enter [1]; rw [h54653 X1 X2 X3 X4 (X1 ◇ (sK0 ◇ X1))]
    conv => enter [1, 2]; rw [l11 X1 sK0 X1 (X2 ◇ X1) X0]
  have l14 : ∀ X1 X2 X3 sK0 X4 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X4)) := by
    intro X1 X2 X3 sK0 X4
    conv => enter [1]; rw [l13 X1 X2 X3 X4 sK0 X1]
    conv => enter [1]; rw [l8 X4 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0)) sK0]
  have l15 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l14 X1 X2 X3 sK0 X1]
    conv => enter [1]; rw [l7 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X1 sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l11 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 sK0 sK0]
  have l18 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l16 X1 X2 X3 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l18 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l17 sK0]
  have l20 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X2]
    conv => enter [1]; rw [h54653 sK0 sK0 X2 X0 X1]
  have l21 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l19 sK0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l20 sK0 X2 sK0 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h54653 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 sK0 (sK0 ◇ sK0) sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l24 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54653 X0 X1 X2 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l23 sK0 (X0 ◇ (X1 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l24 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54654 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54654 G := by
  have l0 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [← h4274 sK3 sK0 sK3]
    conv => enter [1]; rw [h4274 sK3 X0 sK3]
  have l1 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK3 X0 sK0
    conv => enter [1]; rw [h4274 sK3 X0 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [h4274 sK3 sK0 sK3]
  have l2 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK0 ◇ (sK3 ◇ sK3))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 sK3]
    conv => enter [1]; rw [l1 sK3 X0 sK0]
  have l3 : ∀ sK2 sK3 sK4 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK0 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 sK4 sK0
    conv => enter [1]; rw [← h4274 sK3 sK2 sK4]
    conv => enter [1]; rw [l0 sK3 sK3 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z u]
  conv => enter [1]; rw [l2 u y w]

theorem Equation4512_54654_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54654 : Equation54654 G) : Equation4274 G := by
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
  have l7 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X2 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h54654 X0 (sK0 ◇ sK0) X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54654 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ X1)]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l8 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l7 X0 sK0 X1 sK0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54654 (sK0 ◇ sK0) sK0 sK0 X0 sK0]
  have l14 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [h4512 X1 (sK0 ◇ (sK0 ◇ sK0)) X2]
    conv => enter [1, 1]; rw [← h54654 X0 sK0 sK0 X1 sK0]
  have l15 : ∀ X1 sK0 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro X1 sK0 X2 X0
    conv => enter [1]; rw [l14 X1 sK0 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l16 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l12 sK0 sK0 X2]
    conv => enter [1]; rw [← l15 X1 sK0 X2 sK0]
  have l17 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0 X1 X2]
  have l18 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h54654 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X1 X2]
  have l19 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [h54654 sK0 sK0 sK0 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l20 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l18 sK0 sK0 X1]
    conv => enter [1]; rw [← l19 sK0 X1 sK0]
  have l21 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54654 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l20 sK0 (X0 ◇ (X1 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [← l21 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54656 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54656 G := by
  have l0 : ∀ X0 sK0 sK3 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro X0 sK0 sK3 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK3 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK3 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro X0 sK0 sK3 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK3 ◇ sK1)]
  have l2 : ∀ X1 sK0 sK3 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ X2)) = ((sK0 ◇ (sK3 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro X1 sK0 sK3 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK3 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK3 ◇ sK1)) sK0 sK3 sK1 X0]
  have l3 : ∀ X0 sK0 sK3 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ X2)) := by
    intro X0 sK0 sK3 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 sK1 (sK0 ◇ (sK3 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 sK1 X2 X0]
  have l4 : ∀ sK1 sK0 sK3 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK1)) ◇ X2)) := by
    intro sK1 sK0 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK3 sK1 X1 X2]
  have l5 : ∀ sK1 sK0 sK3 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK3 ◇ sK1)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro X0 sK1 sK0 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK1))) := by
    intro X1 X0 X2 sK1 sK0 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u y]

theorem Equation4512_54656_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54656 : Equation54656 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l5 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l6 sK0 sK2]
  have l12 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54656 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l14 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54656 X0 X1 X2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X1 ◇ sK0)]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54656 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54656 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l8 sK0 (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54656 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l18 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h54656 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [l12 sK0 sK2 (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l19 : ∀ X0 sK1 sK0 sK2 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0 sK2 X2
    conv => enter [1]; rw [h54656 X0 sK1 (sK0 ◇ sK2) X0 X2]
    conv => enter [1]; rw [l15 X0 X2 (sK1 ◇ X0) sK0]
  have l20 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [h54656 X0 sK0 sK2 X0 X2]
    conv => enter [1]; rw [l15 X0 X2 (sK0 ◇ X0) sK0]
  have l21 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h54656 X0 sK0 sK0 X0 X2]
    conv => enter [1]; rw [l15 X0 X2 (sK0 ◇ X0) sK0]
  have l22 : ∀ X0 sK1 sK0 sK2 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)) := by
    intro X0 sK1 sK0 sK2 X2
    conv => enter [1]; rw [l19 X0 sK1 sK0 sK2 X2]
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ sK0)) X2 (sK0 ◇ sK0) sK0]
  have l23 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [l20 X0 sK0 sK2 X2]
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ sK0)) X2 (sK0 ◇ sK0) sK0]
  have l24 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l21 X0 sK0 X2]
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ sK0)) X2 (sK0 ◇ sK0) sK0]
  have l25 : ∀ X0 sK1 sK0 sK2 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (X2 ◇ sK0)) := by
    intro X0 sK1 sK0 sK2 X2
    conv => enter [1]; rw [l22 X0 sK1 sK0 sK2 X2]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0 sK0]
  have l26 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (X2 ◇ sK0)) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [l23 X0 sK0 sK2 X2]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0 sK0]
  have l27 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l24 X0 sK0 X2]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0 sK0]
  have l28 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l25 X0 sK1 sK0 sK2 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [← l25 (X0 ◇ X1) sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK2))]
  have l30 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l29 sK0 X0 X1 sK1 sK2]
  have l31 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l28 sK0 X0 sK1 sK2]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l31 sK0 sK0 sK0 sK0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l32 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [← l36 sK0 X0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l37 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l39 : ∀ X1 X2 X3 sK0 sK2 X4 X0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK2) ◇ (X4 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0 sK2 X4 X0
    conv => enter [1]; rw [h54656 X1 X2 X3 (sK0 ◇ sK2) X4]
    conv => enter [1, 2, 2]; rw [l26 X2 sK0 sK2 X0]
  have l40 : ∀ X1 X2 X3 sK0 sK2 X4 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (X4 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0 sK2 X4
    conv => enter [1]; rw [l39 X1 X2 X3 sK0 sK2 X4 X1]
    conv => enter [1]; rw [l18 (sK0 ◇ sK2) X4 ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) sK0 sK2]
  have l41 : ∀ X1 X2 X3 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0 sK2
    conv => enter [1]; rw [l40 X1 X2 X3 sK0 sK2 X1]
    conv => enter [1]; rw [l17 (sK0 ◇ sK0) (sK0 ◇ sK2) (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l42 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l41 X1 X2 X3 sK0 X1]
    conv => enter [1]; rw [l17 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l43 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l42 X1 X2 X3 sK0]
    conv => enter [1]; rw [l16 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l44 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l43 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l38 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l45 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l27 X0 sK0 X0]
    conv => enter [1]; rw [← l27 X1 sK0 X0]
  have l46 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l26 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l47 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l26 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l48 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l47 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l44 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 sK0]
  have l49 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l46 sK1 sK0 sK2]
    conv => enter [1]; rw [← l48 sK1 sK0 sK2 X0]
  have l50 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l49 sK1 sK0 sK2 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l50 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54657 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54657 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK3 ◇ sK0)]
  have l1 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK3 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro X1 sK0 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK3 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK3 ◇ sK0)) sK0 sK3 X0]
  have l3 : ∀ X0 sK0 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK3 (sK0 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK0 sK3 X2 X0]
  have l4 : ∀ sK1 sK0 sK3 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro sK1 sK0 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK3 X1 X2]
  have l5 : ∀ sK1 sK0 sK3 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK3 ◇ sK0)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK1 sK0 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro X1 X0 X2 sK1 sK0 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u y]

theorem Equation4512_54657_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54657 : Equation54657 G) : Equation4274 G := by
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
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK2]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK2)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l5 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l6 sK0 sK2]
  have l12 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK2) X0]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54657 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l14 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54657 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ sK0)]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54657 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l8 sK0 (X1 ◇ sK0)]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54657 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 (X1 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ (X1 ◇ sK2))) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h54657 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [l12 sK0 sK2 (X1 ◇ sK2)]
  have l18 : ∀ X0 sK1 sK0 sK2 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)) := by
    intro X0 sK1 sK0 sK2 X2
    conv => enter [1]; rw [h54657 X0 sK1 (sK0 ◇ sK2) X0 X2]
    conv => enter [1]; rw [l14 X0 X2 (sK1 ◇ X2) sK0]
  have l19 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [h54657 X0 sK0 sK2 X0 X2]
    conv => enter [1]; rw [l14 X0 X2 (sK0 ◇ X2) sK0]
  have l20 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h54657 X0 sK0 sK0 X0 X2]
    conv => enter [1]; rw [l14 X0 X2 (sK0 ◇ X2) sK0]
  have l21 : ∀ X0 sK1 sK0 sK2 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (X2 ◇ sK0)) := by
    intro X0 sK1 sK0 sK2 X2
    conv => enter [1]; rw [l18 X0 sK1 sK0 sK2 X2]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0 sK0]
  have l22 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (X2 ◇ sK0)) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [l19 X0 sK0 sK2 X2]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0 sK0]
  have l23 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l20 X0 sK0 X2]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0 sK0]
  have l24 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l21 X0 sK1 sK0 sK2 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [← l21 (X0 ◇ X1) sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK2))]
  have l26 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l25 sK0 X0 X1 sK1 sK2]
  have l27 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l24 sK0 X0 sK1 sK2]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l27 sK0 sK0 sK0 sK0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l28 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l32 sK0 X0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l35 : ∀ X1 X2 X3 X4 sK0 sK2 X0 : G, (X1 ◇ (X2 ◇ X3)) = (X4 ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro X1 X2 X3 X4 sK0 sK2 X0
    conv => enter [1]; rw [h54657 X1 X2 X3 X4 (sK0 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l22 X2 sK0 sK2 X0]
  have l36 : ∀ X1 X2 X3 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK2))) := by
    intro X1 X2 X3 sK0 sK2
    conv => enter [1]; rw [l35 X1 X2 X3 X1 sK0 sK2 X1]
    conv => enter [1]; rw [l17 X1 (sK0 ◇ sK2) ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) sK0 sK2]
  have l37 : ∀ X1 X2 X3 sK0 sK2 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0 sK2
    conv => enter [1]; rw [l36 X1 X2 X3 sK0 sK2]
    conv => enter [1]; rw [l16 (sK0 ◇ sK0) (sK0 ◇ sK2) ((sK0 ◇ sK2) ◇ sK2) sK0]
  have l38 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l37 X1 X2 X3 sK0 X1]
    conv => enter [1]; rw [l16 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ X1) ◇ (sK0 ◇ sK0)) sK0]
  have l39 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l38 X1 X2 X3 sK0]
    conv => enter [1]; rw [l15 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) sK0]
  have l40 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l39 X1 X2 X3 sK0]
    conv => enter [1]; rw [← l34 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l41 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l23 X0 sK0 X0]
    conv => enter [1]; rw [← l23 X1 sK0 X0]
  have l42 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l22 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l43 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l22 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l44 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l43 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l40 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 sK0]
  have l45 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l42 sK1 sK0 sK2]
    conv => enter [1]; rw [← l44 sK1 sK0 sK2 X0]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l45 sK1 sK0 sK2 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l46 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54658 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54658 G := by
  have l0 : ∀ X0 sK0 sK4 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK4 ◇ sK1))) := by
    intro X0 sK0 sK4 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK4 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK4 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK1)))) := by
    intro X0 sK0 sK4 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK4 ◇ sK1)]
  have l2 : ∀ X1 sK0 sK4 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK4 ◇ sK1)) ◇ X2)) = ((sK0 ◇ (sK4 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK1)))) := by
    intro X1 sK0 sK4 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK4 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK4 ◇ sK1)) sK0 sK4 sK1 X0]
  have l3 : ∀ X0 sK0 sK4 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK1)) ◇ X2)) := by
    intro X0 sK0 sK4 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK4 sK1 (sK0 ◇ (sK4 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK0 sK4 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK4 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK1)) ◇ X2)) := by
    intro sK2 sK0 sK4 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK4 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK4 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK4 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK4 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK4 ◇ sK1)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK4 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK4 ◇ sK1))) := by
    intro X0 sK2 sK0 sK4 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK4 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK4 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK4 ◇ sK1))) := by
    intro X1 X0 X2 sK2 sK0 sK4 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK4 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l7 x y z w u y v]

@[equational_result]
theorem Equation54658_implies_Equation4274 (G : Type*) [Magma G] (h54658 : Equation54658 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54658 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54658 X4 sK0 sK0 X0 X0 X0]
  have l1 : ∀ X0 sK0 sK2 X4 : G, (X0 ◇ (sK0 ◇ sK2)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK2 X4
    conv => enter [1]; rw [h54658 X0 sK0 sK2 X0 X0 X0]
    conv => enter [1]; rw [← h54658 X4 sK0 sK0 X0 X0 X0]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l1 X0 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54659 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54659 G := by
  have l0 : ∀ X0 sK0 sK4 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK4 ◇ sK2))) := by
    intro X0 sK0 sK4 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK4 ◇ sK2)]
  have l1 : ∀ X0 sK0 sK4 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK2)))) := by
    intro X0 sK0 sK4 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK4 ◇ sK2)]
  have l2 : ∀ X1 sK0 sK4 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK4 ◇ sK2)) ◇ X2)) = ((sK0 ◇ (sK4 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK2)))) := by
    intro X1 sK0 sK4 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK4 ◇ sK2)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK4 ◇ sK2)) sK0 sK4 sK2 X0]
  have l3 : ∀ X0 sK0 sK4 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK2)) ◇ X2)) := by
    intro X0 sK0 sK4 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK4 sK2 (sK0 ◇ (sK4 ◇ sK2))]
    conv => enter [1]; rw [← l2 X1 sK0 sK4 sK2 X2 X0]
  have l4 : ∀ sK1 sK0 sK4 sK2 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK2)) ◇ X2)) := by
    intro sK1 sK0 sK4 sK2 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK4 sK2 X1 X2]
  have l5 : ∀ sK1 sK0 sK4 sK2 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK2))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK4 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK4 sK2 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK4 ◇ sK2)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK4 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK2))) := by
    intro X0 sK1 sK0 sK4 sK2
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK4 sK2 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK4 sK2 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK2))) := by
    intro X1 X0 X2 sK1 sK0 sK4 sK2
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK4 sK2]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u z x]

theorem Equation4512_54659_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54659 : Equation54659 G) : Equation4274 G := by
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
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54659 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X2 ◇ X0)]
  have l12 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54659 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (X2 ◇ X0)]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54659 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X2 ◇ X0)]
  have l14 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l12 X0 X1 X2 sK1 sK0 sK2]
    conv => enter [1]; rw [l13 (sK1 ◇ (sK0 ◇ sK2)) X2 X0 sK0]
  have l15 : ∀ sK0 sK2 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [← l13 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [h54659 sK2 sK0 sK0 X1 X2]
  have l16 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l14 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l17 : ∀ sK0 sK2 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [l10 sK0 sK2]
    conv => enter [1]; rw [l15 sK0 sK2 X1 X2]
  have l18 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l16 X0 X1 X2 sK0 X0 X0]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ X0)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l19 : ∀ sK0 sK2 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X2
    conv => enter [1, 2]; rw [← l8 sK0 sK2]
    conv => enter [1]; rw [l17 sK0 sK2 X1 X2]
  have l20 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l18 X0 X1 X2 sK0]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l21 : ∀ sK0 sK2 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK2)]
    conv => enter [1]; rw [l19 sK0 sK2 X1 X2]
  have l22 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l20 X0 X1 X2 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l22 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [l7 sK0]
  have l24 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l23 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [l21 sK0 sK2 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ sK2))]
  have l26 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l21 sK0 sK2 sK0 sK0]
  have l27 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l24 sK0 sK0 (sK0 ◇ (sK0 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l25 sK0 sK2 sK0 sK0 sK0]
  have l28 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l26 sK0 sK2]
    conv => enter [1]; rw [← l27 sK0 sK2]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l24 X0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l24 (sK0 ◇ sK0) sK0 X0 sK0]
  have l31 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1]; rw [← l28 sK0 sK2]
  have l32 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l24 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l31 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l33 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK2]
    conv => enter [1]; rw [l29 sK0 X0]
  have l34 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l32 sK1 sK0 sK2]
    conv => enter [1]; rw [l33 sK0 sK2 X0]
  have l35 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l34 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l24 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l35 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54660 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54660 G := by
  have l0 : ∀ X0 sK0 sK4 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK4 ◇ sK3))) := by
    intro X0 sK0 sK4 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK4 ◇ sK3)]
  have l1 : ∀ X0 sK0 sK4 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK3)))) := by
    intro X0 sK0 sK4 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK4 ◇ sK3)]
  have l2 : ∀ X1 sK0 sK4 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK4 ◇ sK3)) ◇ X2)) = ((sK0 ◇ (sK4 ◇ sK3)) ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK3)))) := by
    intro X1 sK0 sK4 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK4 ◇ sK3)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK4 ◇ sK3)) sK0 sK4 sK3 X0]
  have l3 : ∀ X0 sK0 sK4 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK3))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK3)) ◇ X2)) := by
    intro X0 sK0 sK4 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK4 sK3 (sK0 ◇ (sK4 ◇ sK3))]
    conv => enter [1]; rw [← l2 X1 sK0 sK4 sK3 X2 X0]
  have l4 : ∀ sK1 sK0 sK4 sK3 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK3)) ◇ X2)) := by
    intro sK1 sK0 sK4 sK3 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK4 sK3 X1 X2]
  have l5 : ∀ sK1 sK0 sK4 sK3 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK4 sK3 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK4 sK3 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK4 ◇ sK3)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK4 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) := by
    intro X0 sK1 sK0 sK4 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK4 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK4 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK3))) := by
    intro X1 X0 X2 sK1 sK0 sK4 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK4 sK3]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u z y]

theorem Equation4512_54660_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54660 : Equation54660 G) : Equation4274 G := by
  have l0 : ∀ X1 sK0 X2 X3 X4 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ (X4 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X2 X3 X4 X0
    conv => enter [1]; rw [h54660 X1 (sK0 ◇ sK0) X2 X3 X4]
    conv => enter [1, 2, 2]; rw [h54660 X2 sK0 sK0 X0 sK0]
  have l1 : ∀ X1 sK0 X2 X3 X4 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ (X4 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X2 X3 X4
    conv => enter [1]; rw [l0 X1 sK0 X2 X3 X4 X1]
    conv => enter [1, 2, 2]; rw [← h54660 sK0 sK0 sK0 X1 sK0]
  have l2 : ∀ X1 sK0 X2 X3 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X3 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X2 X3
    conv => enter [1]; rw [l1 X1 sK0 X2 X3 X1]
    conv => enter [1, 2]; rw [← h54660 sK0 sK0 sK0 X1 sK0]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [h54660 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 X1 sK0 X2 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54660 sK0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54660 X0 sK0 sK0 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 X1]
    conv => enter [1]; rw [← l5 sK0 X1 sK0]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← h54660 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54662 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54662 G := by
  have l0 : ∀ X0 sK0 sK4 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK4 ◇ sK1))) := by
    intro X0 sK0 sK4 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK4 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK4 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK1)))) := by
    intro X0 sK0 sK4 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK4 ◇ sK1)]
  have l2 : ∀ X1 sK0 sK4 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK4 ◇ sK1)) ◇ X2)) = ((sK0 ◇ (sK4 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK1)))) := by
    intro X1 sK0 sK4 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK4 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK4 ◇ sK1)) sK0 sK4 sK1 X0]
  have l3 : ∀ X0 sK0 sK4 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK1)) ◇ X2)) := by
    intro X0 sK0 sK4 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK4 sK1 (sK0 ◇ (sK4 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK0 sK4 sK1 X2 X0]
  have l4 : ∀ sK1 sK0 sK4 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK1)) ◇ X2)) := by
    intro sK1 sK0 sK4 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK4 sK1 X1 X2]
  have l5 : ∀ sK1 sK0 sK4 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK4 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK4 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK4 ◇ sK1)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK4 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK1))) := by
    intro X0 sK1 sK0 sK4
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK4 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK4 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK1))) := by
    intro X1 X0 X2 sK1 sK0 sK4
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u z]

theorem Equation4512_54662_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54662 : Equation54662 G) : Equation4274 G := by
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
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X3 X2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X3 ◇ X2))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro sK0 X3 X2 X0 X1
    conv => enter [1]; rw [← l3 sK0 (X3 ◇ X2)]
    conv => enter [1, 2]; rw [h54662 (sK0 ◇ sK0) X3 X2 X0 X1]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X2 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54662 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X2 ◇ sK0)]
  have l11 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK2) ◇ (X2 ◇ sK0)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h54662 X0 X1 X2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (X2 ◇ sK0)]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54662 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X2 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l11 X0 X1 X2 sK0 X0]
    conv => enter [1]; rw [l12 (sK0 ◇ X0) X2 sK0 sK0]
  have l14 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X2 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l9 sK0 sK0 X2 X0 X1]
    conv => enter [1, 2]; rw [l10 (sK0 ◇ (sK0 ◇ sK0)) sK0 X2 sK0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l13 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l14 sK0 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X2 ◇ sK0)]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l15 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l18 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l10 (sK0 ◇ (sK0 ◇ sK0)) X2 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 X0 X1 X2]
  have l19 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l17 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 X0 X1 X2]
  have l21 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l19 X0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l19 (sK0 ◇ sK0) sK0 X0 sK0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l22 sK0]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l19 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l28 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l26 sK1 sK0 sK2]
    conv => enter [1]; rw [l27 sK0 X0]
  have l29 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l28 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l19 X0 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l29 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54663 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54663 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK4 ◇ sK0))) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK4 ◇ sK0)]
  have l1 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK0)))) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK4 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK4 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK4 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK4 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK4 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK4 ◇ sK0)))) := by
    intro X1 sK0 sK4 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK4 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK4 ◇ sK0)) sK0 sK4 X0]
  have l3 : ∀ X0 sK0 sK4 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK4 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 sK4 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK4 (sK0 ◇ (sK4 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK0 sK4 X2 X0]
  have l4 : ∀ sK1 sK0 sK4 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK4 ◇ sK0)) ◇ X2)) := by
    intro sK1 sK0 sK4 X1 X2
    conv => enter [1]; rw [l3 sK1 sK0 sK4 X1 X2]
  have l5 : ∀ sK1 sK0 sK4 X1 X0 : G, (sK1 ◇ (sK0 ◇ (sK4 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 sK4 X1 X0
    conv => enter [1]; rw [l4 sK1 sK0 sK4 X1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK4 ◇ sK0)) sK1]
  have l6 : ∀ X0 sK1 sK0 sK4 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK0))) := by
    intro X0 sK1 sK0 sK4
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK1 sK0 sK4 X0 X0]
  have l7 : ∀ X1 X0 X2 sK1 sK0 sK4 : G, (X1 ◇ (X0 ◇ X2)) = (sK1 ◇ (sK0 ◇ (sK4 ◇ sK0))) := by
    intro X1 X0 X2 sK1 sK0 sK4
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l7 x y z w u z]

theorem Equation4512_54663_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54663 : Equation54663 G) : Equation4274 G := by
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
  have l5 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X2 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h54663 X0 X1 X2 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (X2 ◇ (sK0 ◇ sK2))]
  have l6 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54663 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 (X2 ◇ sK0)]
  have l7 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [l5 X0 X1 X2 X0 sK0 sK2]
    conv => enter [1]; rw [l6 (X0 ◇ (sK0 ◇ sK2)) X2 (sK0 ◇ sK2) sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l7 X0 X1 X2 sK0 X0]
    conv => enter [1]; rw [l6 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ X0) sK0 sK0]
  have l9 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l8 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l9 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l10 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54663 sK0 sK0 sK0 X0 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l15 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1 sK0]
    conv => enter [1]; rw [← l14 sK0 X1 sK0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0 X1]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54663 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l16 sK0 (X0 ◇ (X2 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l17 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54664 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54664 G := by
  have l0 : ∀ X0 sK0 sK5 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK5 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK5 ◇ sK1))) := by
    intro X0 sK0 sK5 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK5 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK5 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK5 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK5 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK5 ◇ sK1)))) := by
    intro X0 sK0 sK5 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK5 ◇ sK1)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK5 ◇ sK1)]
  have l2 : ∀ X1 sK0 sK5 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK5 ◇ sK1)) ◇ X2)) = ((sK0 ◇ (sK5 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK5 ◇ sK1)))) := by
    intro X1 sK0 sK5 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK5 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK5 ◇ sK1)) sK0 sK5 sK1 X0]
  have l3 : ∀ X0 sK0 sK5 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK5 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK5 ◇ sK1)) ◇ X2)) := by
    intro X0 sK0 sK5 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK5 sK1 (sK0 ◇ (sK5 ◇ sK1))]
    conv => enter [1]; rw [← l2 X1 sK0 sK5 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK5 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK5 ◇ sK1))) = (X1 ◇ ((sK0 ◇ (sK5 ◇ sK1)) ◇ X2)) := by
    intro sK2 sK0 sK5 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK5 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK5 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK5 ◇ sK1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK5 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK5 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK5 ◇ sK1)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK5 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK5 ◇ sK1))) := by
    intro X0 sK2 sK0 sK5 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK5 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK5 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK5 ◇ sK1))) := by
    intro X1 X0 X2 sK2 sK0 sK5 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK5 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l7 x y z w u z v]

theorem Equation4512_54664_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54664 : Equation54664 G) : Equation4274 G := by
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
  have l4 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54664 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54664 X4 sK0 sK0 X0 X0 X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0]
  have l7 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h54664 X0 sK0 sK0 (sK0 ◇ sK0) sK0 sK2]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l7 sK0 sK2 sK0]
  have l9 : ∀ X0 sK0 X1 X2 sK2 X3 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK2) ◇ X3))) := by
    intro X0 sK0 X1 X2 sK2 X3
    conv => enter [1, 2]; rw [l8 sK0 sK2]
    conv => enter [1]; rw [h54664 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK2) X1 X2 X3]
  have l10 : ∀ sK0 X1 X2 sK2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK2) ◇ X3))) := by
    intro sK0 X1 X2 sK2 X3
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X1 X2 sK2 X3]
  have l11 : ∀ X1 sK0 sK2 X0 X2 : G, (X1 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro X1 sK0 sK2 X0 X2
    conv => enter [1, 2]; rw [← l3 sK0 sK2 X0]
    conv => enter [1]; rw [← h54664 X2 sK0 sK2 X1 (sK0 ◇ sK0) X0]
  have l12 : ∀ sK0 X2 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [l10 sK0 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK2 sK0 X2]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54677 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54677 G := by
  have l0 : ∀ X0 sK0 sK1 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK3)]
  have l1 : ∀ X0 sK0 sK1 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro X0 sK0 sK1 sK3 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK3)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK1 ◇ sK3)]
  have l2 : ∀ X1 sK0 sK1 sK3 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK3)) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK3)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK3)))) := by
    intro X1 sK0 sK1 sK3 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK1 ◇ sK3)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK3)) sK0 sK1 sK3 X0]
  have l3 : ∀ X0 sK0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK3)) ◇ X2)) := by
    intro X0 sK0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 sK3 (sK0 ◇ (sK1 ◇ sK3))]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 sK3 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 sK3 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK3)) ◇ X2)) := by
    intro sK2 sK0 sK1 sK3 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 sK3 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 sK3 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 sK3 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 sK3 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK3)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 sK3 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 sK3 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 sK3 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro X1 X0 X2 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1 sK3]
  intro x y z w u v
  conv => enter [1]; rw [l7 x y z w u v x]

theorem Equation4512_54677_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54677 : Equation54677 G) : Equation4274 G := by
  have l0 : ∀ X3 X4 X5 X0 sK0 : G, (X3 ◇ (X4 ◇ (X5 ◇ X0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X3 X4 X5 X0 sK0
    conv => enter [1]; rw [← h54677 X0 X3 (X3 ◇ (sK0 ◇ sK0)) X3 X4 X5]
    conv => enter [1, 2]; rw [← h54677 sK0 sK0 sK0 X3 X3 sK0]
  have l1 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X2 X0 X1
    conv => enter [1, 1]; rw [h54677 sK0 sK0 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
  have l2 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l1 sK0 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) X2]
  have l3 : ∀ X2 sK0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X2 sK0
    conv => enter [1]; rw [← l0 X2 X2 (sK0 ◇ sK0) X2 sK0]
    conv => enter [1]; rw [← l2 sK0 X2 X2 X2]
  have l4 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [h54677 sK0 sK0 sK0 X2 sK0 sK0]
    conv => enter [1]; rw [l3 X2 sK0]
  have l5 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54677 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0)) X0 X0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [← l5 y x z x]

@[equational_result]
theorem Equation4274_implies_Equation54678 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54678 G := by
  have l0 : ∀ X0 sK0 sK1 sK4 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK4))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK4))) := by
    intro X0 sK0 sK1 sK4 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK4)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK4)]
  have l1 : ∀ X0 sK0 sK1 sK4 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK4))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK4)))) := by
    intro X0 sK0 sK1 sK4 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK4)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK1 ◇ sK4)]
  have l2 : ∀ X1 sK0 sK1 sK4 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK4)) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK4)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK4)))) := by
    intro X1 sK0 sK1 sK4 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK1 ◇ sK4)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK4)) sK0 sK1 sK4 X0]
  have l3 : ∀ X0 sK0 sK1 sK4 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK4))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK4)) ◇ X2)) := by
    intro X0 sK0 sK1 sK4 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 sK4 (sK0 ◇ (sK1 ◇ sK4))]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 sK4 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 sK4 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK4)) ◇ X2)) := by
    intro sK2 sK0 sK1 sK4 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 sK4 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 sK4 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 sK4 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 sK4 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK4)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 sK4 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) := by
    intro X0 sK2 sK0 sK1 sK4
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 sK4 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 sK4 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK4))) := by
    intro X1 X0 X2 sK2 sK0 sK1 sK4
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1 sK4]
  intro x y z w u v
  conv => enter [1]; rw [l7 x y z w u v y]

theorem Equation4512_54678_implies_Equation4274 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54678 : Equation54678 G) : Equation4274 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54678 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54678 X4 sK0 sK0 X0 X0 X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l1 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l7 : ∀ X2 X3 sK0 X0 X1 : G, (X2 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X2 X3 sK0 X0 X1
    conv => enter [1, 2, 2]; rw [l4 sK0]
    conv => enter [1]; rw [← h54678 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 X2 X3 sK0]
  have l8 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [← l7 X2 X0 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l6 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l8 X0 sK0 X1 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54678 X0 sK0 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54680 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54680 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK1 ◇ sK2)]
  have l2 : ∀ X1 sK0 sK1 sK2 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK0 sK1 sK2 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK1 ◇ sK2)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2 X0]
  have l3 : ∀ X0 sK0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2)) := by
    intro X0 sK0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 sK2 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2)) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 sK2 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK2)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l7 x y z w u v]

@[equational_result]
theorem Equation54680_implies_Equation4274 (G : Type*) [Magma G] (h54680 : Equation54680 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54680 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54680 X4 sK0 sK0 X0 X0 X0]
  have l1 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h54680 X1 X2 X3 X1 X1 X1]
    conv => enter [1]; rw [← h54680 X0 sK0 sK0 X1 X1 X1]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l1 X0 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54681 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54681 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK1 ◇ sK0)]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4274 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4274 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4274 sK0 X0 (sK1 ◇ sK0)]
  have l2 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [← h4274 (sK0 ◇ (sK1 ◇ sK0)) X1 X2]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1 X0]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2)) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l2 X1 sK0 sK1 X2 X0]
  have l4 : ∀ sK2 sK0 sK1 X1 X2 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2)) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X1 X2]
  have l5 : ∀ sK2 sK0 sK1 X1 X0 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4274 X0 (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h4274 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 X0 X0]
  have l7 : ∀ X1 X0 X2 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 X0 X2 sK2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l7 x y z w u v]

@[equational_result]
theorem Equation54681_implies_Equation4274 (G : Type*) [Magma G] (h54681 : Equation54681 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54681 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54681 X4 sK0 sK0 X0 X0 X0]
  have l1 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h54681 X1 X2 X3 X1 X1 X1]
    conv => enter [1]; rw [← h54681 X0 sK0 sK0 X1 X1 X1]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l1 X0 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation4274_implies_Equation54682 (G : Type*) [Magma G] (h4274 : Equation4274 G) : Equation54682 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4274 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4274 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h4274 sK1 X0 (sK1 ◇ sK1)]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1]; rw [h4274 sK1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4274 sK1 sK0 sK1]
    conv => enter [1]; rw [h4274 sK1 X0 sK1]
  have l4 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4274 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4274 sK1 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 sK0]
  have l6 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ X2)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [← h4274 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l6 x y z u v]
  conv => enter [1]; rw [l5 u v w]

@[equational_result]
theorem Equation54682_implies_Equation4274 (G : Type*) [Magma G] (h54682 : Equation54682 G) : Equation4274 G := by
  have l0 : ∀ X0 sK0 X4 : G, (X0 ◇ (sK0 ◇ sK0)) = (X4 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X4
    conv => enter [1]; rw [h54682 X0 sK0 sK0 X0 X0 X0]
    conv => enter [1]; rw [← h54682 X4 sK0 sK0 X0 X0 X0]
  have l1 : ∀ X1 X2 X3 X0 sK0 : G, (X1 ◇ (X2 ◇ X3)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 X3 X0 sK0
    conv => enter [1]; rw [h54682 X1 X2 X3 X1 X1 X1]
    conv => enter [1]; rw [← h54682 X0 sK0 sK0 X1 X1 X1]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l1 X0 sK0 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

end Semigroup5
