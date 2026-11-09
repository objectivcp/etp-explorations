import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_42195_implies_Equation41737 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42195 : Equation42195 G) : Equation41737 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_42195_implies_Equation41741 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation41741 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l2 sK2 sK3 sK2]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2]
  have l4 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ sK0) = (sK2 ◇ sK3) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l3 z w x]

theorem Equation43_42195_implies_Equation42225 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation42225 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l2 sK2 sK3 sK2]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2]
  have l4 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK2]
    conv => enter [1]; rw [← l2 sK2 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l4 x y w]
  conv => enter [1]; rw [l3 x w z]

theorem Equation43_42195_implies_Equation42238 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation42238 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l2 sK3 sK4 sK3]
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) sK3]
  have l5 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ sK0) = (sK3 ◇ sK4) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l3 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK3 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l5 x y w u]
  conv => enter [1]; rw [l4 w u z]

theorem Equation43_4512_42195_implies_Equation41747 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42195 : Equation42195 G) : Equation41747 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_42195_implies_Equation41761 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation41761 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l2 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l4 z y x]
  conv => enter [1]; rw [l3 z y x]

theorem Equation43_42195_implies_Equation41763 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation41763 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l2 sK2 (sK2 ◇ sK3) sK2]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) sK2]
  have l4 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ sK3) sK1]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l3 z w x]

theorem Equation43_42195_implies_Equation42254 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation42254 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation43_42195_implies_Equation42258 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation42258 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ (sK3 ◇ sK4)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4)))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l2 sK3 (sK3 ◇ sK4) sK3]
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4))) sK3]
  have l5 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ sK0) = (sK3 ◇ (sK3 ◇ sK4)) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l3 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK3 (sK3 ◇ sK4) sK1]
  intro x y z w u
  conv => enter [1]; rw [l5 x y w u]
  conv => enter [1]; rw [l4 w u z]

theorem Equation43_4512_42195_implies_Equation41751 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42195 : Equation42195 G) : Equation41751 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK3 ◇ sK0)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = ((sK3 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK0) (sK1 ◇ sK2) X0]
  have l3 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l0 (sK3 ◇ sK0) (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK2)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 X0]
  have l5 : ∀ X2 sK1 X1 X0 sK2 : G, (X2 ◇ sK1) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro X2 sK1 X1 X0 sK2
    conv => enter [1]; rw [h42195 X2 sK1 X1 (X0 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [l4 sK1 X0 sK2]
  have l6 : ∀ X2 sK2 X1 X0 sK3 sK0 : G, (X2 ◇ sK2) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro X2 sK2 X1 X0 sK3 sK0
    conv => enter [1]; rw [h42195 X2 sK2 X1 ((sK3 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK2 (sK3 ◇ sK0) X0]
  have l7 : ∀ X1 X2 X0 sK1 sK2 sK3 sK0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))) = (X2 ◇ (sK3 ◇ sK0)) := by
    intro X1 X2 X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2, 2, 2]; rw [l3 X0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h42195 X2 (sK3 ◇ sK0) X1 ((sK1 ◇ sK2) ◇ X0)]
  have l8 : ∀ sK3 sK0 sK1 sK2 X1 X0 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK3 sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [h42195 (sK3 ◇ sK0) (sK1 ◇ sK2) X1 X0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK2 sK3 sK0 X0]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l10 : ∀ sK3 sK0 sK1 sK2 X1 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) = (X1 ◇ X1) := by
    intro sK3 sK0 sK1 sK2 X1
    conv => enter [1]; rw [l8 sK3 sK0 sK1 sK2 X1 sK3]
    conv => enter [1]; rw [← l9 X1 X1 ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK3)]
  have l11 : ∀ X2 X0 sK3 sK0 : G, (X2 ◇ X0) = (X2 ◇ (sK3 ◇ sK0)) := by
    intro X2 X0 sK3 sK0
    conv => enter [1]; rw [h42195 X2 X0 X2 (X2 ◇ (X2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l7 X2 X2 X0 X2 X2 sK3 sK0]
  have l12 : ∀ X2 X0 sK2 : G, (X2 ◇ X0) = (X2 ◇ sK2) := by
    intro X2 X0 sK2
    conv => enter [1]; rw [h42195 X2 X0 X2 (sK2 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← l6 X2 sK2 X2 X0 X2 X2]
  have l13 : ∀ X2 X0 sK1 : G, (X2 ◇ X0) = (X2 ◇ sK1) := by
    intro X2 X0 sK1
    conv => enter [1]; rw [h42195 X2 X0 X2 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l5 X2 sK1 X2 X0 X2]
  have l14 : ∀ sK1 sK2 sK3 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ X1) := by
    intro sK1 sK2 sK3 sK0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l10 sK3 sK0 sK1 sK2 X1]
  have l15 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l16 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK2 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [l11 X0 (sK1 ◇ (X0 ◇ sK1)) sK3 sK0]
  have l17 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ sK2) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l12 X0 (sK3 ◇ sK0) sK2]
  have l18 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ sK1) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l17 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l13 X0 sK2 sK1]
  have l19 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l18 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h43 X0 sK1]
  intro x y z w
  conv => enter [1]; rw [← l19 x y z w y]
  conv => enter [1]; rw [l19 x y z w (x ◇ (y ◇ (z ◇ w)))]

theorem Equation43_42195_implies_Equation41768 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation41768 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK3 sK4 sK1 X0 : G, (sK3 ◇ (sK4 ◇ sK1)) = (X0 ◇ X0) := by
    intro sK3 sK4 sK1 X0
    conv => enter [1]; rw [h43 sK3 (sK4 ◇ sK1)]
    conv => enter [1]; rw [l2 (sK4 ◇ sK1) sK3 X0]
  have l4 : ∀ sK3 sK4 sK1 sK2 : G, (sK3 ◇ (sK4 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK3 sK4 sK1 sK2
    conv => enter [1]; rw [l3 sK3 sK4 sK1 sK3]
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) sK3]
  have l5 : ∀ sK3 sK4 sK1 sK2 sK0 : G, (sK3 ◇ (sK4 ◇ sK1)) = (sK2 ◇ sK0) := by
    intro sK3 sK4 sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK3 sK4 sK1 sK3]
    conv => enter [1]; rw [← l2 sK2 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [← l5 z w u x y]
  conv => enter [1]; rw [l4 z w u x]

theorem Equation43_42195_implies_Equation42204 (G : Type*) [Magma G] (h43 : Equation43 G) (h42195 : Equation42195 G) : Equation42204 G := by
  have l0 : ∀ X2 X0 X3 X1 : G, (X2 ◇ X0) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42195 X2 X0 X3 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X0 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42195 X2 X0 X2 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h42195 X0 X1 X2 X2]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = (X3 ◇ X3) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l0 X2 X0 X3 X2]
    conv => enter [1]; rw [← l1 X3 X3 ((X0 ◇ X2) ◇ X2)]
  have l3 : ∀ sK3 sK4 sK1 sK2 : G, (sK3 ◇ (sK4 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1)))) := by
    intro sK3 sK4 sK1 sK2
    conv => enter [1]; rw [l2 sK3 (sK4 ◇ sK1) sK3]
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ sK1))) sK3]
  have l4 : ∀ sK3 sK0 sK4 sK1 : G, (sK3 ◇ sK0) = (sK3 ◇ (sK4 ◇ sK1)) := by
    intro sK3 sK0 sK4 sK1
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [← l2 sK3 (sK4 ◇ sK1) sK3]
  intro x y z w u
  conv => enter [1]; rw [l4 x y w u]
  conv => enter [1]; rw [l3 x w u z]

@[equational_result]
theorem Equation41768_implies_Equation38 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation41768_implies_Equation41805 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation41768_implies_Equation41882 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_41768_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41768 : Equation41768 G) : Equation42405 G := by
  have l0 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l1 : ∀ sK4 sK5 X0 : G, ((sK4 ◇ sK5) ◇ X0) = (sK4 ◇ (X0 ◇ sK5)) := by
    intro sK4 sK5 X0
    conv => enter [1]; rw [← h4512 sK4 sK5 X0]
    conv => enter [1, 2]; rw [h43 sK5 X0]
  have l2 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK2 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l3 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l4 : ∀ sK6 sK3 sK1 sK2 sK0 X0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK6 sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l3 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6 X0]
  have l5 : ∀ sK4 sK5 X0 : G, (sK4 ◇ sK5) = ((sK4 ◇ sK5) ◇ X0) := by
    intro sK4 sK5 X0
    conv => enter [1]; rw [l3 sK4 sK5 (X0 ◇ sK5)]
    conv => enter [1]; rw [← l1 sK4 sK5 X0]
  have l6 : ∀ sK1 sK2 sK0 sK4 sK5 sK3 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK4 ◇ sK5)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK4) := by
    intro sK1 sK2 sK0 sK4 sK5 sK3
    conv => enter [1, 2]; rw [l3 sK4 sK5 sK3]
    conv => enter [1]; rw [← l2 sK3 sK1 sK2 sK0 sK4]
  have l7 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK4 ◇ sK5)) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l4 sK6 sK3 sK1 sK2 sK0 sK4]
    conv => enter [1]; rw [← l6 sK1 sK2 sK0 sK4 sK5 sK3]
  have l8 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK4 ◇ sK5) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l7 sK6 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) (sK4 ◇ sK5)]
  have l9 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK4 sK5 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK6 sK3 sK1 sK2 sK0 sK4 sK5]
  intro x y z w u v r
  conv => enter [1]; rw [l9 x y z w u v r]

@[equational_result]
theorem Equation41768_implies_Equation41732 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (x ◇ x)))]

theorem Equation43_4512_41768_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41768 : Equation41768 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 (X1 ◇ sK0)]
    conv => enter [1]; rw [← l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation41768_implies_Equation41734 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation43_4512_41768_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41768 : Equation41768 G) : Equation42230 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l8 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X1]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
  have l12 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ sK2) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l11 sK0 sK1 X0]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation43_4512_41768_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41768 : Equation41768 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l4 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l5 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l4 sK0 sK3 X0]
  have l6 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l7 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l6 sK0 sK3 X0]
  have l8 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ X0) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ (sK1 ◇ sK2)) X1]
    conv => enter [1]; rw [l6 sK1 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) X0]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 sK2]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l10 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
    conv => enter [1]; rw [← l8 X1 sK1 sK2 sK1]
  have l11 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l7 sK3 sK0 (X0 ◇ sK3)]
    conv => enter [1]; rw [l5 sK0 X0 sK3]
  have l12 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK0) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l7 sK3 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0]
  have l13 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l9 sK1 sK2 sK0]
    conv => enter [1]; rw [← l12 sK1 sK3 sK0 sK2]
  have l14 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK3 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK2 sK3 sK0]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l14 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l15 z w x y]

@[equational_result]
theorem Equation41768_implies_Equation41740 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation43_4512_41768_implies_Equation42222 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41768 : Equation41768 G) : Equation42222 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1)]
  have l4 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 (sK0 ◇ (sK1 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l6 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ X0) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l4 sK1 X0 (sK2 ◇ X1)]
    conv => enter [1]; rw [l0 sK1 sK2 X1]
  have l7 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l4 (sK1 ◇ sK1) X0 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK2]
  have l8 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 X1 sK2]
  have l9 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [l7 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK2]
  have l10 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 X0 sK2]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [l12 x y z]
  conv => enter [1]; rw [l4 z (x ◇ x) (z ◇ (z ◇ (x ◇ x)))]

theorem Equation43_4512_41768_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41768 : Equation41768 G) : Equation42237 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l3 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) (sK2 ◇ sK2)]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l4 sK1 sK2]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
  have l7 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l8 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l7 sK0 sK3 X0]
  have l9 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l10 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l11 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l10 sK0 sK3 X0]
  have l12 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l10 sK1 X0 (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
    conv => enter [1]; rw [l9 sK1 X1 sK2]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l14 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1]
    conv => enter [1]; rw [l12 sK1 sK1 X1 sK2]
  have l15 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l11 sK3 sK0 (X0 ◇ sK3)]
    conv => enter [1]; rw [l8 sK0 X0 sK3]
  have l16 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l11 sK3 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0]
  have l17 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l13 sK1 sK2 sK0]
    conv => enter [1]; rw [← l16 sK1 sK3 sK0 sK2]
  have l18 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK3 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 sK2 sK3 sK0]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l14 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l18 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l19 z w x y]

@[equational_result]
theorem Equation41768_implies_Equation41737 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41737 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (y ◇ z)))]

@[equational_result]
theorem Equation41768_implies_Equation41741 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41741 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (z ◇ w)))]

theorem Equation43_41768_implies_Equation42225 (G : Type*) [Magma G] (h43 : Equation43 G) (h41768 : Equation41768 G) : Equation42225 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ sK1) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [h43 sK1 X0]
  have l2 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [l0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]
  conv => enter [1]; rw [l0 z (x ◇ w) (z ◇ (z ◇ (x ◇ w)))]

theorem Equation43_4512_41768_implies_Equation42238 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41768 : Equation41768 G) : Equation42238 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK4) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK4) X0]
  have l2 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK4)) X0]
  have l3 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ (sK3 ◇ sK4)) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) (sK3 ◇ sK4)]
    conv => enter [1]; rw [← l1 sK2 sK3 sK4 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
  have l4 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← l3 sK2 sK3 sK4]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) (sK3 ◇ sK4)]
  have l5 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (sK2 ◇ ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK4]
  have l6 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l5 sK2 sK3 sK4]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK4) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  have l8 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) X0]
  have l10 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l12 : ∀ sK2 X0 X1 sK3 sK4 : G, (sK2 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 X0 X1 sK3 sK4
    conv => enter [1]; rw [l10 sK2 X0 (X1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
    conv => enter [1]; rw [l9 sK2 X1 sK3 sK4]
  have l13 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l10 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) X0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
    conv => enter [1]; rw [l6 sK2 sK3 sK4]
  have l14 : ∀ sK2 sK3 sK4 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4 X1
    conv => enter [1]; rw [l10 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) sK2]
    conv => enter [1]; rw [l12 sK2 sK2 X1 sK3 sK4]
  have l15 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 (X0 ◇ sK1)]
    conv => enter [1]; rw [l8 sK0 X0 sK1]
  have l16 : ∀ sK2 sK1 sK0 sK3 sK4 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ sK0) := by
    intro sK2 sK1 sK0 sK3 sK4
    conv => enter [1, 2]; rw [l11 sK1 sK0 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1]; rw [← l2 sK2 sK3 sK4 sK0]
  have l17 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l13 sK2 sK3 sK4 sK0]
    conv => enter [1]; rw [← l16 sK2 sK1 sK0 sK3 sK4]
  have l18 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l15 sK1 sK0 sK2]
    conv => enter [1]; rw [← l17 sK2 sK3 sK4 sK1 sK0]
  have l19 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l18 sK1 sK0 sK2 sK3 sK4]
    conv => enter [1]; rw [← l14 sK2 sK3 sK4 (sK2 ◇ (sK3 ◇ sK4))]
  intro x y z w u
  conv => enter [1]; rw [l19 x y z w u]

@[equational_result]
theorem Equation41768_implies_Equation41747 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41747 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y (x ◇ (y ◇ (y ◇ z)))]

@[equational_result]
theorem Equation41768_implies_Equation41761 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41761 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

@[equational_result]
theorem Equation41768_implies_Equation41763 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41763 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x y (x ◇ (z ◇ (z ◇ w)))]

theorem Equation43_4512_41768_implies_Equation42254 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41768 : Equation41768 G) : Equation42254 G := by
  have l0 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK2 ◇ sK3)) X0]
  have l1 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l2 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l0 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l3 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l2 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) (sK2 ◇ (sK2 ◇ sK3))]
  have l4 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l5 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X1) = (sK2 ◇ X0) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l1 sK2 sK3 X1]
    conv => enter [1]; rw [l4 sK2 (X1 ◇ (sK2 ◇ sK3)) X0]
  have l6 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X1) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l4 sK2 (sK2 ◇ sK3) sK2]
    conv => enter [1]; rw [← l5 sK2 sK3 X1 sK2]
  have l7 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l4 sK1 (sK2 ◇ (sK2 ◇ sK3)) (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [← l0 sK1 sK2 sK3 X0]
  have l8 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X0 ◇ sK1) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l4 sK1 (sK2 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [h43 sK1 X0]
  have l9 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l7 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [l3 sK1 sK2 sK3]
  have l10 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l6 sK2 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))))]
    conv => enter [1]; rw [← l9 sK1 sK2 sK3]
  have l11 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l4 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l10 sK2 sK3 sK1]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK3]
    conv => enter [1]; rw [l4 sK3 sK1 sK0]
  have l13 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK2 sK3 sK2]
    conv => enter [1]; rw [l12 sK2 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l13 w x y]
  conv => enter [1]; rw [l11 w x z]
  conv => enter [1]; rw [l4 z (w ◇ (w ◇ x)) (z ◇ (w ◇ (w ◇ x)))]

theorem Equation43_41768_implies_Equation42258 (G : Type*) [Magma G] (h43 : Equation43 G) (h41768 : Equation41768 G) : Equation42258 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [h43 sK0 X0]
  have l3 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l2 sK1 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 sK0 (sK3 ◇ (sK3 ◇ sK4))]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]
  conv => enter [1]; rw [l0 z (w ◇ (w ◇ u)) (z ◇ (w ◇ (w ◇ u)))]

@[equational_result]
theorem Equation41768_implies_Equation41751 (G : Type*) [Magma G] (h41768 : Equation41768 G) : Equation41751 G := by
  have l0 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x y (x ◇ (y ◇ (z ◇ w)))]

theorem Equation43_4512_41768_implies_Equation42195 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41768 : Equation41768 G) : Equation42195 G := by
  have l0 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l1 : ∀ X0 X1 X5 : G, (X0 ◇ X1) = (X0 ◇ X5) := by
    intro X0 X1 X5
    conv => enter [1]; rw [h41768 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h41768 X0 X5 X0 X0 X0]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK3 (sK2 ◇ (sK3 ◇ sK0))]
  have l3 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = ((sK2 ◇ sK3) ◇ sK1) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l1 sK2 sK3 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK2)))]
    conv => enter [1]; rw [← l2 sK2 sK3 sK1 sK2]
  have l4 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l3 sK2 sK3 sK1]
    conv => enter [1]; rw [h43 (sK2 ◇ sK3) sK1]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ sK3) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l4 sK2 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [← l5 z x y w]

theorem Equation43_4512_41751_implies_Equation38 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ sK1) X1]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l10 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l8 X2 X0 X1]
  have l12 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [h41751 X1 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1, 2, 2]; rw [l10 sK0 X0 sK1]
  have l13 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h41751 X1 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 X0]
  have l14 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h41751 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [l11 X0 X3 (X1 ◇ X2)]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l16 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41751 sK1 X0 X1 X2]
    conv => enter [1]; rw [l3 sK0 sK1 (sK1 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l17 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l16 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK0 ◇ sK1) (X0 ◇ (X1 ◇ X2))]
  have l18 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ X3) := by
    intro X0 X3
    conv => enter [1]; rw [l15 X0 ((X0 ◇ X0) ◇ X3)]
    conv => enter [1]; rw [← l14 X0 X3 X0 X0]
  have l19 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [h41751 X1 sK0 (sK0 ◇ X1) X1]
    conv => enter [1]; rw [← l13 X1 sK0 X1 X1]
  have l20 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41751 X1 X0 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l12 X1 sK0 X0 X1]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41751 (sK0 ◇ sK1) X0 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 sK1 X0 sK0 sK0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1]; rw [← l18 (sK0 ◇ sK0) (sK1 ◇ X0)]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← l19 (sK0 ◇ sK0) sK0]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) sK0]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l24 sK0 sK1 X0]
  have l26 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l9 X0 (sK0 ◇ sK1) X1]
    conv => enter [1, 2]; rw [← l25 sK0 sK1 X0]
  have l27 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l25 sK0 sK1 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 (sK0 ◇ sK1) X1 X0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l20 sK0 sK0 sK0]
  have l29 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [l19 X1 sK0]
    conv => enter [1]; rw [← l26 X0 sK0 sK1 X1]
  have l30 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ sK0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l20 X0 ((sK0 ◇ X0) ◇ X1) sK0]
    conv => enter [1]; rw [← l29 X1 sK0 X0 X0]
  have l31 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ sK0) := by
    intro sK0 X1
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [l30 sK0 sK0 X1]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1]; rw [h43 X0 sK0]
  intro x y
  conv => enter [1]; rw [l32 x y]

theorem Equation43_4512_41751_implies_Equation41805 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ sK3 sK4 sK1 sK0 X0 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK3 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK4 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1, 2]; rw [l3 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 sK3 (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l5 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l4 sK2 sK3 sK4 sK1 sK0 X0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  have l7 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l8 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l9 : ∀ X1 sK2 sK3 sK4 sK1 sK0 X0 : G, (X1 ◇ sK2) = (X1 ◇ (X1 ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0))) := by
    intro X1 sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [h41751 X1 sK2 X0 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l2 sK2 sK3 sK4 sK1 sK0 X0]
  have l10 : ∀ X1 sK3 sK4 sK1 sK0 X0 : G, (X1 ◇ sK3) = (X1 ◇ (X1 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro X1 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [h41751 X1 sK3 X0 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l3 sK3 sK4 sK1 sK0 X0]
  have l11 : ∀ X1 sK2 sK3 sK4 sK1 sK0 X0 : G, (X1 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X1 ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0))) := by
    intro X1 sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [h41751 X1 (sK2 ◇ sK3) X0 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l5 sK2 sK3 sK4 sK1 sK0 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 (X0 ◇ X1)]
  have l14 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ X1) (sK1 ◇ sK0)]
  have l15 : ∀ X1 sK2 sK3 : G, (X1 ◇ (sK2 ◇ sK3)) = (X1 ◇ X1) := by
    intro X1 sK2 sK3
    conv => enter [1]; rw [l11 X1 sK2 sK3 X1 X1 X1 X1]
    conv => enter [1]; rw [← l12 X1 ((sK2 ◇ (sK3 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l16 : ∀ X1 sK3 : G, (X1 ◇ sK3) = (X1 ◇ X1) := by
    intro X1 sK3
    conv => enter [1]; rw [l10 X1 sK3 X1 X1 X1 X1]
    conv => enter [1]; rw [← l12 X1 ((sK3 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X1)]
  have l17 : ∀ X1 sK2 : G, (X1 ◇ sK2) = (X1 ◇ X1) := by
    intro X1 sK2
    conv => enter [1]; rw [l9 X1 sK2 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← l12 X1 ((sK2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l18 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l8 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l19 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l7 X3 X2 X3 X3]
    conv => enter [1]; rw [← l12 X3 ((X3 ◇ X3) ◇ X2)]
  have l20 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 X0 X1]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [l19 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← l15 (sK1 ◇ sK0) sK2 sK3]
  have l23 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ sK0) = ((sK2 ◇ sK3) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l22 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) (sK2 ◇ sK3)]
  have l24 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ sK0) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l23 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l19 (sK2 ◇ sK3) (sK1 ◇ sK0)]
  have l25 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ sK0) = ((sK2 ◇ sK3) ◇ sK3) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l24 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l16 (sK2 ◇ sK3) sK3]
  have l26 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ sK0) = (sK3 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [l25 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [h43 (sK2 ◇ sK3) sK3]
  have l27 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ sK0) = (sK3 ◇ sK3) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l26 sK1 sK0 sK3 sK1]
    conv => enter [1]; rw [l19 sK3 (sK1 ◇ sK3)]
  have l28 : ∀ sK1 sK0 sK3 sK2 : G, (sK1 ◇ sK0) = (sK3 ◇ sK2) := by
    intro sK1 sK0 sK3 sK2
    conv => enter [1]; rw [l27 sK1 sK0 sK3]
    conv => enter [1]; rw [← l17 sK3 sK2]
  have l29 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK1 ◇ sK0) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [h43 sK2 sK3]
    conv => enter [1]; rw [l28 sK3 sK2 sK1 sK0]
  have l30 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l29 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l19 sK2 sK1]
  have l31 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ X0) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1, 1]; rw [l30 sK1 sK0 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 X0]
  have l32 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l30 sK1 sK0 sK2]
    conv => enter [1]; rw [← l1 sK2 sK2 X0]
  have l33 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ sK2) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l32 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l19 sK2 (sK2 ◇ X0)]
  have l34 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ X0) = (sK2 ◇ sK2) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l31 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [l19 sK2 (sK2 ◇ X0)]
  have l35 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l30 sK1 sK0 sK1]
    conv => enter [1]; rw [← l33 X0 sK1 sK0 sK1]
  have l36 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l30 sK1 sK0 sK1]
    conv => enter [1]; rw [← l34 sK1 sK0 X0 sK1]
  have l37 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l35 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l38 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = (sK1 ◇ sK0) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← l18 X0 X1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l37 sK1 sK0 X0 X1]
  have l39 : ∀ sK1 sK0 sK4 : G, (sK1 ◇ sK0) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [l36 sK1 sK0 sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  have l40 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l39 sK1 sK0 sK4]
  have l41 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l40 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l19 (sK2 ◇ sK3) (sK1 ◇ sK0)]
  have l42 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l38 sK1 sK0 (sK2 ◇ sK3) (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l41 sK2 sK3 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l38 x y w u]
  conv => enter [1]; rw [l42 w u x y z]

theorem Equation43_4512_41751_implies_Equation41882 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK3 sK5 sK2 sK0 sK1 X0 : G, ((sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK3 ◇ (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK3 sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l5 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l6 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l7 : ∀ X1 sK3 sK5 sK2 sK0 sK1 X0 : G, (X1 ◇ sK3) = (X1 ◇ (X1 ◇ ((sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro X1 sK3 sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [h41751 X1 sK3 X0 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l2 sK3 sK5 sK2 sK0 sK1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [l1 sK0 sK1 (X0 ◇ X1)]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ X1) (sK0 ◇ sK1)]
  have l11 : ∀ X1 sK3 : G, (X1 ◇ sK3) = (X1 ◇ X1) := by
    intro X1 sK3
    conv => enter [1]; rw [l7 X1 sK3 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← l8 X1 ((sK3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l12 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l6 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l13 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l5 X3 X2 X3 X3]
    conv => enter [1]; rw [← l8 X3 ((X3 ◇ X3) ◇ X2)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l13 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK3) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l11 (sK0 ◇ sK1) sK3]
  have l16 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ sK1) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l15 sK0 sK1 sK3]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK3]
  have l17 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ sK1) = (sK3 ◇ sK3) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l16 sK0 sK1 sK3]
    conv => enter [1]; rw [l13 sK3 (sK0 ◇ sK1)]
  have l18 : ∀ sK0 sK1 X0 sK3 : G, ((sK0 ◇ sK1) ◇ X0) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK0 sK1 X0 sK3
    conv => enter [1, 1]; rw [l17 sK0 sK1 sK3]
    conv => enter [1]; rw [← l4 sK3 X0 sK3]
  have l19 : ∀ sK0 sK1 X0 sK3 : G, ((sK0 ◇ sK1) ◇ X0) = (sK3 ◇ sK3) := by
    intro sK0 sK1 X0 sK3
    conv => enter [1]; rw [l18 sK0 sK1 X0 sK3]
    conv => enter [1]; rw [l13 sK3 (X0 ◇ sK3)]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 X0 sK0]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK2]
  have l22 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l20 sK0 sK1 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 (sK0 ◇ sK1) X1 X0]
  have l23 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ sK1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l12 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l22 sK0 sK1 X0 X1]
  have l24 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK5) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [h43 sK5 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1]; rw [← l21 sK0 sK1 sK2]
  have l25 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l24 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l13 (sK0 ◇ sK1) sK5]
  have l26 : ∀ sK0 sK1 sK5 sK2 : G, (sK0 ◇ sK1) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK5 sK2
    conv => enter [1]; rw [l23 sK0 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l25 sK5 sK2 sK0 sK1]
  have l27 : ∀ sK3 sK5 sK2 sK0 sK1 : G, (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK3 ◇ sK3) := by
    intro sK3 sK5 sK2 sK0 sK1
    conv => enter [1, 2]; rw [← l26 sK0 sK1 sK5 sK2]
    conv => enter [1]; rw [l13 sK3 (sK0 ◇ sK1)]
  have l28 : ∀ sK0 sK1 sK3 sK5 sK2 : G, (sK0 ◇ sK1) = (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3 sK5 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK3 sK3]
    conv => enter [1]; rw [← l27 sK3 sK5 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l23 x y u v]
  conv => enter [1]; rw [l28 u v x z w]

theorem Equation43_4512_41751_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation42405 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [h43 (sK2 ◇ sK0) sK1]
  have l2 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l3 : ∀ sK3 sK1 sK2 sK0 sK6 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK6 ◇ X0)) = ((sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 sK6 X0
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6 X0]
    conv => enter [1, 1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l5 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l1 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l6 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l2 sK1 sK2 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l7 : ∀ sK6 sK3 sK1 sK2 sK0 X0 : G, ((sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ sK6)) := by
    intro sK6 sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l3 sK3 sK1 sK2 sK0 sK6 X0]
    conv => enter [1, 2]; rw [h43 sK6 X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l9 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ X0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK2]
  have l10 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l11 : ∀ X1 sK2 sK0 sK1 X0 : G, (X1 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0))) := by
    intro X1 sK2 sK0 sK1 X0
    conv => enter [1]; rw [h41751 X1 (sK2 ◇ sK0) X0 sK1]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK2 sK0 X0]
  have l12 : ∀ X1 sK1 sK2 sK0 sK3 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X1 ◇ ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0))) := by
    intro X1 sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h41751 X1 (sK1 ◇ (sK2 ◇ sK0)) X0 sK3]
    conv => enter [1, 2, 2]; rw [← l6 sK3 sK1 sK2 sK0 X0]
  have l13 : ∀ X1 sK3 sK1 sK2 sK0 sK6 X0 : G, (X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (X1 ◇ ((sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0))) := by
    intro X1 sK3 sK1 sK2 sK0 sK6 X0
    conv => enter [1]; rw [h41751 X1 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0 sK6]
    conv => enter [1, 2, 2]; rw [← l7 sK6 sK3 sK1 sK2 sK0 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l15 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ sK2) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h41751 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [l9 sK0 sK2 (X0 ◇ X1)]
  have l16 : ∀ sK4 sK5 X0 X1 : G, (sK4 ◇ sK5) = (sK4 ◇ ((X0 ◇ X1) ◇ (sK4 ◇ sK5))) := by
    intro sK4 sK5 X0 X1
    conv => enter [1]; rw [h41751 sK4 sK5 X0 X1]
    conv => enter [1, 2]; rw [l4 sK4 sK5 (X0 ◇ X1)]
  have l17 : ∀ sK4 sK5 X0 X1 : G, (sK4 ◇ sK5) = ((sK4 ◇ sK5) ◇ (sK4 ◇ (X0 ◇ X1))) := by
    intro sK4 sK5 X0 X1
    conv => enter [1]; rw [l16 sK4 sK5 X0 X1]
    conv => enter [1]; rw [l4 sK4 (X0 ◇ X1) (sK4 ◇ sK5)]
  have l18 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ sK2) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l15 sK0 sK2 X0 X1]
    conv => enter [1]; rw [l4 sK0 (X0 ◇ X1) (sK2 ◇ sK0)]
  have l19 : ∀ X1 sK3 sK1 sK2 sK0 : G, (X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X1 ◇ X1) := by
    intro X1 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l13 X1 sK3 sK1 sK2 sK0 X1 X1]
    conv => enter [1]; rw [← l14 X1 ((X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X1)]
  have l20 : ∀ X1 sK1 sK2 sK0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ X1) := by
    intro X1 sK1 sK2 sK0
    conv => enter [1]; rw [l12 X1 sK1 sK2 sK0 X1 X1]
    conv => enter [1]; rw [← l14 X1 ((X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1)]
  have l21 : ∀ X1 sK2 sK0 : G, (X1 ◇ (sK2 ◇ sK0)) = (X1 ◇ X1) := by
    intro X1 sK2 sK0
    conv => enter [1]; rw [l11 X1 sK2 sK0 X1 X1]
    conv => enter [1]; rw [← l14 X1 ((X1 ◇ (sK2 ◇ sK0)) ◇ X1)]
  have l22 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l10 X3 X2 X3 X3]
    conv => enter [1]; rw [← l14 X3 ((X3 ◇ X3) ◇ X2)]
  have l23 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h43 sK2 sK0]
    conv => enter [1]; rw [l18 sK0 sK2 X0 X1]
  have l24 : ∀ sK4 sK5 : G, (sK4 ◇ sK5) = ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) := by
    intro sK4 sK5
    conv => enter [1]; rw [l17 sK4 sK5 sK4 sK4]
    conv => enter [1]; rw [l22 (sK4 ◇ sK5) (sK4 ◇ (sK4 ◇ sK4))]
  have l25 : ∀ sK4 sK5 : G, (sK4 ◇ sK5) = ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) := by
    intro sK4 sK5
    conv => enter [1]; rw [l17 sK4 sK5 sK4 sK4]
    conv => enter [1]; rw [l22 (sK4 ◇ sK5) (sK4 ◇ (sK4 ◇ sK4))]
  have l26 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l23 sK2 sK0 sK2 sK2]
    conv => enter [1]; rw [l22 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK2))]
  have l27 : ∀ sK4 sK5 : G, ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) = (sK4 ◇ sK4) := by
    intro sK4 sK5
    conv => enter [1]; rw [← l24 sK4 sK5]
    conv => enter [1]; rw [l22 sK4 sK5]
  have l28 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l27 sK4 sK5]
    conv => enter [1]; rw [← l19 sK4 sK3 sK1 sK2 sK0]
  have l29 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK4) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK4 sK5 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 sK4 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l30 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l29 sK4 sK5 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l22 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK4]
  have l31 : ∀ sK3 sK1 sK2 sK0 sK4 sK5 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) := by
    intro sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l20 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1 sK2 sK0]
    conv => enter [1]; rw [← l30 sK4 sK5 sK3 sK1 sK2 sK0]
  have l32 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK4 sK5]
    conv => enter [1]; rw [← l31 sK3 sK1 sK2 sK0 sK4 sK5]
  have l33 : ∀ sK4 sK5 sK1 sK2 sK0 sK3 : G, (sK4 ◇ sK5) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l32 sK4 sK5 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK1 ◇ (sK2 ◇ sK0))]
  have l34 : ∀ sK4 sK5 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK4 sK5 sK1 sK2 sK0 sK4]
    conv => enter [1]; rw [l22 (sK1 ◇ (sK2 ◇ sK0)) (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l35 : ∀ sK4 sK5 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK5 sK1 sK2 sK0
    conv => enter [1]; rw [l34 sK4 sK5 sK1 sK2 sK0]
    conv => enter [1]; rw [← l21 (sK1 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l36 : ∀ sK4 sK5 sK2 sK0 sK1 : G, (sK4 ◇ sK5) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l35 sK4 sK5 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
  have l37 : ∀ sK4 sK5 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK5 sK2 sK0
    conv => enter [1]; rw [l36 sK4 sK5 sK2 sK0 sK4]
    conv => enter [1]; rw [l22 (sK2 ◇ sK0) (sK4 ◇ (sK2 ◇ sK0))]
  have l38 : ∀ X0 sK4 sK5 sK2 sK0 : G, (X0 ◇ (sK4 ◇ sK5)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro X0 sK4 sK5 sK2 sK0
    conv => enter [1, 2]; rw [l37 sK4 sK5 sK2 sK0]
    conv => enter [1]; rw [l8 X0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
  have l39 : ∀ X0 sK4 sK5 sK2 sK0 : G, (X0 ◇ (sK4 ◇ sK5)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro X0 sK4 sK5 sK2 sK0
    conv => enter [1]; rw [l38 X0 sK4 sK5 sK2 sK0]
    conv => enter [1]; rw [l22 (sK2 ◇ sK0) ((sK2 ◇ sK0) ◇ X0)]
  have l40 : ∀ sK2 sK0 X0 sK4 sK5 : G, (sK2 ◇ sK0) = (X0 ◇ (sK4 ◇ sK5)) := by
    intro sK2 sK0 X0 sK4 sK5
    conv => enter [1]; rw [l26 sK2 sK0]
    conv => enter [1]; rw [← l39 X0 sK4 sK5 sK2 sK0]
  have l41 : ∀ sK4 sK5 sK2 sK0 : G, (sK4 ◇ sK5) = (sK2 ◇ sK0) := by
    intro sK4 sK5 sK2 sK0
    conv => enter [1]; rw [l37 sK4 sK5 sK2 sK0]
    conv => enter [1]; rw [← l26 sK2 sK0]
  have l42 : ∀ sK1 sK2 sK0 sK4 sK5 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK4 ◇ sK5) ◇ sK1) := by
    intro sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [h43 sK1 (sK2 ◇ sK0)]
    conv => enter [1, 1]; rw [l41 sK2 sK0 sK4 sK5]
  have l43 : ∀ sK1 sK2 sK0 sK4 sK5 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) := by
    intro sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l42 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [l22 (sK4 ◇ sK5) sK1]
  have l44 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l40 sK2 sK0 (sK2 ◇ sK2) sK2 sK2]
    conv => enter [1]; rw [← l43 sK1 sK2 sK0 sK2 sK2]
  have l45 : ∀ sK4 sK5 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK5 sK1 sK2 sK0
    conv => enter [1]; rw [l41 sK4 sK5 sK2 sK0]
    conv => enter [1]; rw [l44 sK2 sK0 sK1]
  have l46 : ∀ sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ sK5) ◇ sK3) := by
    intro sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 1]; rw [← l45 sK4 sK5 sK1 sK2 sK0]
  have l47 : ∀ sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) := by
    intro sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l46 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [l22 (sK4 ◇ sK5) sK3]
  have l48 : ∀ sK2 sK0 sK3 sK1 : G, (sK2 ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK3 sK1
    conv => enter [1]; rw [l40 sK2 sK0 (sK2 ◇ sK2) sK2 sK2]
    conv => enter [1]; rw [← l47 sK3 sK1 sK2 sK0 sK2 sK2]
  have l49 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l41 sK4 sK5 sK2 sK0]
    conv => enter [1]; rw [l48 sK2 sK0 sK3 sK1]
  have l50 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK4 ◇ sK5) ◇ sK6) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [h43 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 1]; rw [← l49 sK4 sK5 sK3 sK1 sK2 sK0]
  have l51 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK4 ◇ sK5) ◇ (sK4 ◇ sK5)) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l50 sK6 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [l22 (sK4 ◇ sK5) sK6]
  have l52 : ∀ sK2 sK0 sK6 sK3 sK1 : G, (sK2 ◇ sK0) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK6 sK3 sK1
    conv => enter [1]; rw [l40 sK2 sK0 (sK2 ◇ sK2) sK2 sK2]
    conv => enter [1]; rw [← l51 sK6 sK3 sK1 sK2 sK0 sK2 sK2]
  have l53 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l41 sK4 sK5 sK2 sK0]
    conv => enter [1]; rw [l52 sK2 sK0 sK6 sK3 sK1]
  intro x y z w u v r
  conv => enter [1]; rw [l53 x y z w u v r]

theorem Equation43_4512_41751_implies_Equation41732 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l6 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l7 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41751 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l1 sK0 (X0 ◇ X1)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41751 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← l2 sK0 (X0 ◇ X1)]
  have l11 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41751 sK0 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ X2))]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [l4 sK0 (X0 ◇ X1)]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0]
  have l14 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l7 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l15 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l6 X3 X2 X3 X3]
    conv => enter [1]; rw [← l8 X3 ((X3 ◇ X3) ◇ X2)]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l15 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l16 sK0 sK0 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l15 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l17 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l18 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1, 1]; rw [← l19 sK0]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l22 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1 (sK0 ◇ sK0)]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l14 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l23 sK0 X0 X1]
  intro x y
  conv => enter [1]; rw [l24 x y x]
  conv => enter [1]; rw [l19 x]

theorem Equation43_4512_41751_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l6 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l7 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41751 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l1 sK0 (X0 ◇ X1)]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41751 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← l2 sK0 (X0 ◇ X1)]
  have l11 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41751 sK0 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ X2))]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [l4 sK0 (X0 ◇ X1)]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0]
  have l14 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l7 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l15 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l6 X3 X2 X3 X3]
    conv => enter [1]; rw [← l8 X3 ((X3 ◇ X3) ◇ X2)]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l15 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l16 sK0 sK0 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l15 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l17 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l18 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1, 1]; rw [← l19 sK0]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l22 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1 (sK0 ◇ sK0)]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l14 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l23 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l24 x y z]
  conv => enter [1]; rw [l19 z]

theorem Equation43_4512_41751_implies_Equation41734 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l2 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l3 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l4 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h41751 X1 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h41751 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41751 X0 X0 X1 (X0 ◇ X0)]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ X1)]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (X0 ◇ X1)]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
  have l11 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ X1)]
  have l12 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ X1) := by
    intro X1 sK0
    conv => enter [1]; rw [l4 X1 sK0 X1 X1]
    conv => enter [1]; rw [l5 X1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X1)))) ◇ X1)]
  have l13 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l3 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l14 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l2 X3 X2 X3 X3]
    conv => enter [1]; rw [l5 X3 ((X3 ◇ X3) ◇ X2)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l14 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l14 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l14 sK0 (sK0 ◇ sK1)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l12 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l12 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l12 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK0 X0]
  have l28 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l27 X0 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ X0)]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l28 X0 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l32 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l29 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l33 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l13 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l32 sK0 sK1 X0 X1]
  have l34 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l33 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l35 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ sK1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l34 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l35 x y x z]
  conv => enter [1]; rw [l35 x z x (x ◇ (x ◇ (x ◇ z)))]

theorem Equation43_4512_41751_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l5 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h41751 X1 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l6 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK2 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h41751 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41751 X0 X0 X1 (X0 ◇ X0)]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ X1)]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (X0 ◇ X1)]
  have l11 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
  have l12 : ∀ X1 sK1 : G, (X1 ◇ sK1) = (X1 ◇ X1) := by
    intro X1 sK1
    conv => enter [1]; rw [l6 X1 sK1 X1 X1]
    conv => enter [1]; rw [l7 X1 ((sK1 ◇ X1) ◇ X1)]
  have l13 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ X1) := by
    intro X1 sK0
    conv => enter [1]; rw [l5 X1 sK0 X1 X1]
    conv => enter [1]; rw [l7 X1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X1)))) ◇ X1)]
  have l14 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l4 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l15 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l3 X3 X2 X3 X3]
    conv => enter [1]; rw [l7 X3 ((X3 ◇ X3) ◇ X2)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l12 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l12 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l15 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l15 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l26 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l27 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l30 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK0 X0]
  have l31 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l30 X0 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ X0)]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l31 X0 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l33 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l32 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l38 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l14 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l37 sK0 sK1 X0 X1]
  have l39 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l38 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l39 x y z x]
  conv => enter [1]; rw [l36 z x]

theorem Equation43_4512_41751_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l2 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l3 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l4 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK2 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l6 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ sK3) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [h41751 sK0 sK3 X0 X1]
    conv => enter [1, 2]; rw [l2 sK0 sK3 (X0 ◇ X1)]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 sK1 (sK1 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ X1)]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (X0 ◇ X1)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
  have l11 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ sK3) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [l6 sK0 sK3 X0 X1]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1) (sK3 ◇ sK0)]
  have l12 : ∀ X1 sK1 : G, (X1 ◇ sK1) = (X1 ◇ X1) := by
    intro X1 sK1
    conv => enter [1]; rw [l4 X1 sK1 X1 X1]
    conv => enter [1]; rw [← l5 X1 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X1)))) ◇ X1)]
  have l13 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l3 X3 X2 X3 X3]
    conv => enter [1]; rw [← l5 X3 ((X3 ◇ X3) ◇ X2)]
  have l14 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ sK0) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l11 sK0 sK3 X0 X1]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l13 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l13 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l17 : ∀ sK3 sK0 : G, (sK3 ◇ sK0) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l14 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l13 (sK3 ◇ sK0) (sK0 ◇ (sK3 ◇ sK3))]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK1]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
  have l20 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = ((sK3 ◇ sK0) ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l17 sK3 sK0]
    conv => enter [1]; rw [← l12 (sK3 ◇ sK0) sK1]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK1]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
  have l23 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l20 sK3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) sK1]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l21 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l26 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l23 sK3 sK0 sK1]
    conv => enter [1]; rw [l13 sK1 (sK3 ◇ sK0)]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [← l24 sK1 sK2]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← l27 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l29 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [← l28 sK1 sK2]
  have l30 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [l29 sK1 sK2]
  have l31 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK3 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l31 x y z w]
  conv => enter [1]; rw [l30 z w]

theorem Equation43_4512_41751_implies_Equation41740 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l5 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h41751 X1 sK0 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l6 : ∀ X1 sK1 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X1)]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ X1)]
  have l11 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l12 : ∀ X1 sK1 : G, (X1 ◇ X1) = (X1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l7 X1 ((sK1 ◇ sK1) ◇ X1)]
    conv => enter [1]; rw [← l6 X1 sK1 X1]
  have l13 : ∀ X1 sK0 : G, (X1 ◇ X1) = (X1 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l7 X1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (X1 ◇ X1)))) ◇ X1)]
    conv => enter [1]; rw [← l5 X1 sK0 X1 X1]
  have l14 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l4 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l15 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l3 X3 X2 X3 X3]
    conv => enter [1]; rw [← l7 X3 ((X3 ◇ X3) ◇ X2)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l15 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l15 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l23 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h43 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h43 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l30 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK0 X0]
  have l31 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l30 X0 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ X0)]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l31 X0 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l33 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l32 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l38 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l14 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l37 sK0 sK1 X0 X1]
  have l39 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l38 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l40 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l39 sK1 sK1 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l40 z x y]
  conv => enter [1]; rw [l39 z z x z]
  conv => enter [1]; rw [l36 x z]

theorem Equation43_4512_41751_implies_Equation42222 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation42222 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l5 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h41751 X1 sK0 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l6 : ∀ X1 sK1 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X1)]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ X1)]
  have l11 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l12 : ∀ X1 sK1 : G, (X1 ◇ X1) = (X1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [l7 X1 ((sK1 ◇ sK1) ◇ X1)]
    conv => enter [1]; rw [← l6 X1 sK1 X1]
  have l13 : ∀ X1 sK0 : G, (X1 ◇ X1) = (X1 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l7 X1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (X1 ◇ X1)))) ◇ X1)]
    conv => enter [1]; rw [← l5 X1 sK0 X1 X1]
  have l14 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l4 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l15 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l3 X3 X2 X3 X3]
    conv => enter [1]; rw [← l7 X3 ((X3 ◇ X3) ◇ X2)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l15 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l15 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l23 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h43 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h43 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l30 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK0 X0]
  have l31 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l30 X0 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ X0)]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l31 X0 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l33 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l32 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l38 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l14 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l37 sK0 sK1 X0 X1]
  have l39 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l38 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l39 x y z x]
  conv => enter [1]; rw [l36 z x]

theorem Equation43_4512_41751_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation42237 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l4 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l5 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK2 X0]
  have l6 : ∀ X1 sK2 X0 : G, (X1 ◇ sK2) = (X1 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK2 X0 sK2]
    conv => enter [1, 2, 2]; rw [← l2 sK2 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l8 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ sK3) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [h41751 sK0 sK3 X0 X1]
    conv => enter [1, 2]; rw [l3 sK0 sK3 (X0 ◇ X1)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 sK1 (sK2 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) (X0 ◇ X1)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (X0 ◇ X1)]
  have l11 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l10 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (X0 ◇ X1)]
  have l12 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (X0 ◇ X1)]
  have l13 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ sK3) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [l8 sK0 sK3 X0 X1]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1) (sK3 ◇ sK0)]
  have l14 : ∀ X1 sK2 : G, (X1 ◇ sK2) = (X1 ◇ X1) := by
    intro X1 sK2
    conv => enter [1]; rw [l6 X1 sK2 X1]
    conv => enter [1]; rw [← l7 X1 ((sK2 ◇ sK2) ◇ X1)]
  have l15 : ∀ X1 sK1 : G, (X1 ◇ sK1) = (X1 ◇ X1) := by
    intro X1 sK1
    conv => enter [1]; rw [l5 X1 sK1 X1 X1]
    conv => enter [1]; rw [← l7 X1 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l16 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l4 X3 X2 X3 X3]
    conv => enter [1]; rw [← l7 X3 ((X3 ◇ X3) ◇ X2)]
  have l17 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ sK0) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l13 sK0 sK3 X0 X1]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l20 : ∀ sK3 sK0 : G, (sK3 ◇ sK0) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l17 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l16 (sK3 ◇ sK0) (sK0 ◇ (sK3 ◇ sK3))]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [← l14 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) sK2]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [← l14 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2]
  have l23 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = ((sK3 ◇ sK0) ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l20 sK3 sK0]
    conv => enter [1]; rw [← l14 (sK3 ◇ sK0) sK2]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l21 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) sK2]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2]
  have l26 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l23 sK3 sK0 sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) sK2]
  have l27 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l16 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
    conv => enter [1]; rw [← l24 sK1 sK2]
  have l28 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l16 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l25 sK1 sK2]
  have l29 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l16 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l26 sK3 sK0 sK2]
  have l30 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l27 sK2 sK1]
    conv => enter [1]; rw [← l15 sK2 sK1]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l28 sK2 sK1]
    conv => enter [1]; rw [← l15 sK2 sK1]
  have l32 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← l29 sK2 sK3 sK0]
    conv => enter [1]; rw [← l15 sK2 sK1]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l30 sK1 sK2]
    conv => enter [1]; rw [h43 sK2 sK1]
  have l34 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [h43 sK2 sK1]
  have l35 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [h43 sK2 sK1]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [l16 sK1 sK2]
  have l37 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [l16 sK1 sK2]
  have l38 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l35 sK3 sK0 sK1 sK3]
    conv => enter [1]; rw [l16 sK1 sK3]
  have l39 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [← l36 sK1 sK2]
  have l40 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← l39 sK1 sK2]
    conv => enter [1]; rw [l16 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l41 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l36 sK1 sK2]
    conv => enter [1]; rw [← l40 sK1 sK2]
  have l42 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l39 sK1 sK2]
    conv => enter [1]; rw [l41 sK1 sK2]
  have l43 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK3 sK0 sK1]
    conv => enter [1]; rw [← l37 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l43 x y z w]
  conv => enter [1]; rw [l42 z w]

theorem Equation43_4512_41751_implies_Equation41737 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41737 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK2)]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0]
  have l11 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l12 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l13 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK0 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 sK2 X0]
  have l14 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK2 X0]
  have l15 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 (sK0 ◇ sK1) X0 sK2]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1 sK2 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l17 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
  have l18 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK1) ◇ sK2) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 (sK0 ◇ sK1) sK2 X0 X1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2 (X0 ◇ X1)]
  have l19 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK1) ◇ sK2) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l8 sK0 sK1 sK2 (X0 ◇ X1)]
  have l20 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l17 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (X0 ◇ X1)]
  have l21 : ∀ X1 sK0 sK1 : G, (X1 ◇ (sK0 ◇ sK1)) = (X1 ◇ X1) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [l15 X1 sK0 sK1 X1 X1]
    conv => enter [1]; rw [← l16 X1 ((sK0 ◇ (sK1 ◇ X1)) ◇ X1)]
  have l22 : ∀ X1 sK1 : G, (X1 ◇ sK1) = (X1 ◇ X1) := by
    intro X1 sK1
    conv => enter [1]; rw [l14 X1 sK1 X1 X1]
    conv => enter [1]; rw [← l16 X1 ((sK1 ◇ X1) ◇ X1)]
  have l23 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ X1) := by
    intro X1 sK0
    conv => enter [1]; rw [l13 X1 sK0 X1 X1 X1]
    conv => enter [1]; rw [← l16 X1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l24 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l12 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l25 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l11 X3 X2 X3 X3]
    conv => enter [1]; rw [← l16 X3 ((X3 ◇ X3) ◇ X2)]
  have l26 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0 X1]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l25 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [← l25 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 sK1 sK0]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [← l21 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK0 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1 sK2]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ sK1)]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 (sK0 ◇ sK1) sK1]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK1 (sK0 ◇ sK1)]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 sK1 sK0]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1 sK2]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l39 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l40 sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2, 1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l43 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ sK0) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l42 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l25 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l41 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l45 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l43 X0 sK0 sK1 sK2]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l44 sK0 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l45 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l48 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l24 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [← l47 sK0 sK1 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l48 x y x y z]
  conv => enter [1]; rw [l46 x y z]

theorem Equation43_4512_41751_implies_Equation41741 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41741 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l2 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l3 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l4 : ∀ X1 sK1 sK2 sK3 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0))) := by
    intro X1 sK1 sK2 sK3 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK2 sK3 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l6 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [h41751 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) (X0 ◇ X1)]
  have l7 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (sK2 ◇ ((X0 ◇ X1) ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h41751 sK2 sK3 X0 X1]
    conv => enter [1, 2]; rw [l0 sK2 sK3 (X0 ◇ X1)]
  have l8 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = ((sK2 ◇ sK3) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l7 sK2 sK3 X0 X1]
    conv => enter [1]; rw [l0 sK2 (X0 ◇ X1) (sK2 ◇ sK3)]
  have l9 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 sK3 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (X0 ◇ X1)]
  have l10 : ∀ X1 sK1 : G, (X1 ◇ sK1) = (X1 ◇ X1) := by
    intro X1 sK1
    conv => enter [1]; rw [l4 X1 sK1 X1 X1 X1]
    conv => enter [1]; rw [← l5 X1 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l11 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l3 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l12 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l2 X3 X2 X3 X3]
    conv => enter [1]; rw [← l5 X3 ((X3 ◇ X3) ◇ X2)]
  have l13 : ∀ sK2 sK3 : G, (sK2 ◇ sK3) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l8 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l12 (sK2 ◇ sK3) (sK2 ◇ (sK2 ◇ sK2))]
  have l14 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK1 sK1]
    conv => enter [1, 2]; rw [← l12 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l15 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = ((sK2 ◇ sK3) ◇ sK1) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l13 sK2 sK3]
    conv => enter [1]; rw [← l10 (sK2 ◇ sK3) sK1]
  have l16 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l14 sK1 sK2 sK3]
    conv => enter [1]; rw [← l10 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) sK1]
  have l17 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l15 sK2 sK3 sK1]
    conv => enter [1]; rw [h43 (sK2 ◇ sK3) sK1]
  have l18 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l16 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) sK1]
  have l19 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ sK1) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l17 sK2 sK3 sK1]
    conv => enter [1]; rw [l12 sK1 (sK2 ◇ sK3)]
  have l20 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l18 sK1 sK2 sK3]
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))]
  have l21 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l19 sK2 sK3 sK1]
    conv => enter [1]; rw [← l20 sK1 sK2 sK3]
  have l22 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ ((sK2 ◇ sK3) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2, 1]; rw [l21 sK2 sK3 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l23 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (sK1 ◇ sK1) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [← l22 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l12 sK1 ((sK2 ◇ sK3) ◇ X0)]
  have l24 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1, 2]; rw [← l21 sK2 sK3 sK1]
    conv => enter [1]; rw [l12 sK1 (sK2 ◇ sK3)]
  have l25 : ∀ sK2 sK3 X0 sK1 : G, (sK2 ◇ sK3) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 X0 sK1
    conv => enter [1]; rw [l19 sK2 sK3 sK1]
    conv => enter [1]; rw [← l23 X0 sK1 sK2 sK3]
  have l26 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l19 sK2 sK3 sK1]
    conv => enter [1]; rw [← l24 sK1 sK2 sK3]
  have l27 : ∀ sK2 sK3 X0 X1 sK1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))))) := by
    intro sK2 sK3 X0 X1 sK1
    conv => enter [1]; rw [l25 sK2 sK3 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))]
  have l28 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ X1) = (sK2 ◇ sK3) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [← l11 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ sK3))))]
    conv => enter [1]; rw [← l27 sK2 sK3 X0 X1 X0]
  intro x y z w
  conv => enter [1]; rw [l28 x y z w]
  conv => enter [1]; rw [l26 z w x]

theorem Equation43_4512_41751_implies_Equation42225 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation42225 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l2 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = (sK2 ◇ (X0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l5 : ∀ X1 sK1 sK2 sK3 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0))) := by
    intro X1 sK1 sK2 sK3 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK2 sK3 X0]
  have l6 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ sK2) = (X1 ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [h41751 X1 sK2 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK2 sK0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l8 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [h41751 sK1 (sK2 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK3) (X0 ◇ X1)]
  have l9 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [h41751 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) (X0 ◇ X1)]
  have l10 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 sK3 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (X0 ◇ X1)]
  have l11 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 sK3 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) (X0 ◇ X1)]
  have l12 : ∀ X1 sK2 : G, (X1 ◇ sK2) = (X1 ◇ X1) := by
    intro X1 sK2
    conv => enter [1]; rw [l6 X1 sK2 X1 X1]
    conv => enter [1]; rw [← l7 X1 ((sK2 ◇ X1) ◇ X1)]
  have l13 : ∀ X1 sK1 : G, (X1 ◇ sK1) = (X1 ◇ X1) := by
    intro X1 sK1
    conv => enter [1]; rw [l5 X1 sK1 X1 X1 X1]
    conv => enter [1]; rw [← l7 X1 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l14 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l4 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l15 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l3 X3 X2 X3 X3]
    conv => enter [1]; rw [← l7 X3 ((X3 ◇ X3) ◇ X2)]
  have l16 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK1 sK1]
    conv => enter [1, 2]; rw [← l15 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l17 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK1 sK1]
    conv => enter [1, 2]; rw [← l15 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  have l18 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l16 sK1 sK2 sK3]
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) sK2]
  have l19 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l17 sK1 sK2 sK3]
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2]
  have l20 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l18 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) sK2]
  have l21 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l19 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2]
  have l22 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK2 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l20 sK1 sK2 sK3]
    conv => enter [1]; rw [l15 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))]
  have l23 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l21 sK1 sK2 sK3]
    conv => enter [1]; rw [l15 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l24 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK2 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l22 sK1 sK2 sK3]
    conv => enter [1]; rw [← l13 sK2 sK1]
  have l25 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l23 sK1 sK2 sK3]
    conv => enter [1]; rw [← l13 sK2 sK1]
  have l26 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l24 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 sK2 sK1]
  have l27 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l25 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 sK2 sK1]
  have l28 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l26 sK1 sK2 sK3]
    conv => enter [1]; rw [l15 sK1 sK2]
  have l29 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l27 sK1 sK2 sK3]
    conv => enter [1]; rw [l15 sK1 sK2]
  have l30 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2]; rw [l28 sK1 sK2 sK3]
    conv => enter [1]; rw [← l0 sK1 sK1 X0]
  have l31 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ sK1) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l30 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [l15 sK1 (sK1 ◇ X0)]
  have l32 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l28 sK1 sK2 sK3]
    conv => enter [1]; rw [← l31 X0 sK1 sK2 sK3]
  have l33 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l29 sK1 sK2 sK3]
    conv => enter [1]; rw [← l28 sK1 sK2 sK3]
  have l34 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1, 2]; rw [← l33 sK1 sK2 sK3]
    conv => enter [1]; rw [l15 sK1 (sK1 ◇ (sK2 ◇ sK3))]
  have l35 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l28 sK1 sK2 sK3]
    conv => enter [1]; rw [← l34 sK1 sK2 sK3]
  have l36 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l33 sK1 sK2 sK3]
    conv => enter [1]; rw [l35 sK1 sK2 sK3]
  have l37 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l32 sK1 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l38 : ∀ X0 X1 sK1 sK2 sK3 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 X1 sK1 sK2 sK3
    conv => enter [1]; rw [← l14 X0 X1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [← l37 sK1 sK2 sK3 X0 X1]
  have l39 : ∀ X0 X1 sK1 sK2 sK3 : G, (X0 ◇ X1) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X0 X1 sK1 sK2 sK3
    conv => enter [1]; rw [l38 X0 X1 sK1 sK2 sK3]
    conv => enter [1]; rw [← l33 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l39 x y z x w]
  conv => enter [1]; rw [l36 z x w]

theorem Equation43_4512_41751_implies_Equation42238 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation42238 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  have l3 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l4 : ∀ X1 sK2 sK3 sK4 X0 : G, (X1 ◇ sK2) = (X1 ◇ (X1 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0))) := by
    intro X1 sK2 sK3 sK4 X0
    conv => enter [1]; rw [h41751 X1 sK2 X0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
    conv => enter [1, 2, 2]; rw [← l1 sK2 sK3 sK4 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41751 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [l2 sK0 sK1 (X0 ◇ X1)]
  have l7 : ∀ sK2 sK3 sK4 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [h41751 sK2 (sK2 ◇ (sK3 ◇ sK4)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) (X0 ◇ X1)]
  have l8 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ sK4) = (sK3 ◇ ((X0 ◇ X1) ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [h41751 sK3 sK4 X0 X1]
    conv => enter [1, 2]; rw [l0 sK3 sK4 (X0 ◇ X1)]
  have l9 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ sK4) = ((sK3 ◇ sK4) ◇ (sK3 ◇ (X0 ◇ X1))) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l8 sK3 sK4 X0 X1]
    conv => enter [1]; rw [l0 sK3 (X0 ◇ X1) (sK3 ◇ sK4)]
  have l10 : ∀ sK2 sK3 sK4 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [l7 sK2 sK3 sK4 X0 X1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) (X0 ◇ X1)]
  have l11 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1) (sK1 ◇ sK0)]
  have l12 : ∀ X1 sK2 : G, (X1 ◇ sK2) = (X1 ◇ X1) := by
    intro X1 sK2
    conv => enter [1]; rw [l4 X1 sK2 X1 X1 X1]
    conv => enter [1]; rw [← l5 X1 ((sK2 ◇ (sK2 ◇ (sK2 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l13 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l3 X3 X2 X3 X3]
    conv => enter [1]; rw [← l5 X3 ((X3 ◇ X3) ◇ X2)]
  have l14 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l11 sK0 sK1 X0 X1]
  have l15 : ∀ sK3 sK4 : G, (sK3 ◇ sK4) = ((sK3 ◇ sK4) ◇ (sK3 ◇ sK4)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l9 sK3 sK4 sK3 sK3]
    conv => enter [1]; rw [l13 (sK3 ◇ sK4) (sK3 ◇ (sK3 ◇ sK3))]
  have l16 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l10 sK2 sK3 sK4 sK2 sK2]
    conv => enter [1, 2]; rw [← l13 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [l13 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
  have l18 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = ((sK3 ◇ sK4) ◇ sK2) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l15 sK3 sK4]
    conv => enter [1]; rw [← l12 (sK3 ◇ sK4) sK2]
  have l19 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ sK2) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l16 sK2 sK3 sK4]
    conv => enter [1]; rw [← l12 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) sK2]
  have l20 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l12 (sK1 ◇ sK0) sK2]
  have l21 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK3 ◇ sK4)) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l18 sK3 sK4 sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK4) sK2]
  have l22 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l19 sK2 sK3 sK4]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) sK2]
  have l23 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK2]
  have l24 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ sK2) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l21 sK3 sK4 sK2]
    conv => enter [1]; rw [l13 sK2 (sK3 ◇ sK4)]
  have l25 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK2 ◇ sK2) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l22 sK2 sK3 sK4]
    conv => enter [1]; rw [l13 sK2 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l23 sK1 sK0 sK2]
    conv => enter [1]; rw [l13 sK2 (sK1 ◇ sK0)]
  have l27 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l24 sK3 sK4 sK2]
    conv => enter [1]; rw [← l25 sK2 sK3 sK4]
  have l28 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (sK2 ◇ sK2) := by
    intro sK2 sK3 sK4
    conv => enter [1, 2]; rw [← l27 sK3 sK4 sK2]
    conv => enter [1]; rw [l13 sK2 (sK3 ◇ sK4)]
  have l29 : ∀ sK3 sK4 sK2 : G, (sK3 ◇ sK4) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK3 sK4 sK2
    conv => enter [1]; rw [l24 sK3 sK4 sK2]
    conv => enter [1]; rw [← l28 sK2 sK3 sK4]
  have l30 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ sK0) = (sK3 ◇ sK4) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l26 sK1 sK0 sK1]
    conv => enter [1]; rw [← l24 sK3 sK4 sK1]
  intro x y z w u
  conv => enter [1]; rw [l30 x y w u]
  conv => enter [1]; rw [l29 w u z]

theorem Equation43_4512_41751_implies_Equation41747 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41747 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK1]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK1 ◇ sK2))]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0]
  have l11 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l12 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l13 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK0 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 sK2 X0]
  have l14 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK2 X0]
  have l15 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 (sK0 ◇ sK1) X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1 sK2 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l17 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (X0 ◇ X1)]
  have l18 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 (sK0 ◇ sK1) (sK1 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2 (X0 ◇ X1)]
  have l19 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l8 sK0 sK1 sK2 (X0 ◇ X1)]
  have l20 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l17 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ X1)]
  have l21 : ∀ X1 sK0 sK1 : G, (X1 ◇ (sK0 ◇ sK1)) = (X1 ◇ X1) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [l15 X1 sK0 sK1 X1 X1]
    conv => enter [1]; rw [← l16 X1 ((sK0 ◇ (sK1 ◇ (sK1 ◇ X1))) ◇ X1)]
  have l22 : ∀ X1 sK1 : G, (X1 ◇ sK1) = (X1 ◇ X1) := by
    intro X1 sK1
    conv => enter [1]; rw [l14 X1 sK1 X1 X1]
    conv => enter [1]; rw [← l16 X1 ((sK1 ◇ (sK1 ◇ X1)) ◇ X1)]
  have l23 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ X1) := by
    intro X1 sK0
    conv => enter [1]; rw [l13 X1 sK0 X1 X1 X1]
    conv => enter [1]; rw [← l16 X1 ((sK0 ◇ (sK0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l24 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l12 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l25 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l11 X3 X2 X3 X3]
    conv => enter [1]; rw [← l16 X3 ((X3 ◇ X3) ◇ X2)]
  have l26 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0 X1]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l25 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l25 sK1 (sK1 ◇ sK2)]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 sK1 sK0]
  have l30 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [← l21 (sK1 ◇ (sK1 ◇ sK2)) sK0 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1 sK2]
  have l32 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK1)]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l34 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [l25 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2))]
  have l35 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l34 sK1 sK2 sK0]
    conv => enter [1]; rw [← l22 (sK0 ◇ sK1) sK1]
  have l36 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l37 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l36 sK1 sK2 sK1]
    conv => enter [1]; rw [l25 sK1 (sK1 ◇ sK1)]
  have l38 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [← l23 sK1 sK0]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [l38 sK1 sK0 sK2]
  have l40 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l39 sK0 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l41 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l40 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 sK0 X0]
  have l42 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ sK0) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l41 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ X0)]
  have l43 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l42 X0 sK1 sK2 sK0]
  have l44 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l43 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l45 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l24 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l44 sK0 sK1 sK2 X0 X1]
  have l46 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l45 X0 X1 X0 sK1 sK2]
    conv => enter [1]; rw [l43 X0 sK1 sK2 sK1]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l43 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [l25 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l48 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l46 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l47 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l46 x y y z]
  conv => enter [1]; rw [l48 y z x]

theorem Equation43_4512_41751_implies_Equation41761 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41761 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l5 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK0 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 sK2 X0]
  have l6 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK2 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l8 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h41751 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (X0 ◇ X1)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ X1)]
  have l11 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (X0 ◇ X1)]
  have l12 : ∀ X1 sK1 : G, (X1 ◇ sK1) = (X1 ◇ X1) := by
    intro X1 sK1
    conv => enter [1]; rw [l6 X1 sK1 X1 X1]
    conv => enter [1]; rw [← l7 X1 ((sK1 ◇ (sK1 ◇ X1)) ◇ X1)]
  have l13 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ X1) := by
    intro X1 sK0
    conv => enter [1]; rw [l5 X1 sK0 X1 X1 X1]
    conv => enter [1]; rw [← l7 X1 ((sK0 ◇ (sK0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l14 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l4 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l15 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l3 X3 X2 X3 X3]
    conv => enter [1]; rw [← l7 X3 ((X3 ◇ X3) ◇ X2)]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [← l15 sK1 (sK1 ◇ sK2)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK1]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK1]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK2]
    conv => enter [1]; rw [l15 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l24 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l26 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 sK1 sK0]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 sK1 sK0]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2 sK0]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l30 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [← l29 sK0 sK1 sK2]
  have l31 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l30 sK1 sK2 sK0]
  have l32 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l31 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l15 sK0 (X0 ◇ (sK1 ◇ sK2))]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l30 sK1 sK2 sK0]
    conv => enter [1]; rw [l15 sK0 (sK1 ◇ sK2)]
  have l34 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2 X0]
  have l35 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [← l33 sK0 sK1 sK2]
  have l36 : ∀ sK1 sK2 X0 X1 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l34 sK1 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l37 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [← l14 X0 X1 (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [← l36 sK1 sK2 X0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l37 x y z y]
  conv => enter [1]; rw [l35 z y x]

theorem Equation43_4512_41751_implies_Equation41763 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41751 : Equation41751 G) : Equation41763 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) X0]
  have l2 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l3 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41751 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X4 ◇ (X0 ◇ X1)) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h41751 X4 (X0 ◇ X1) X2 X3]
  have l5 : ∀ X1 sK1 sK2 sK3 X0 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ X0))) := by
    intro X1 sK1 sK2 sK3 X0
    conv => enter [1]; rw [h41751 X1 sK1 X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK2 sK3 X0]
  have l6 : ∀ X1 sK2 sK3 X0 : G, (X1 ◇ sK2) = (X1 ◇ (X1 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0))) := by
    intro X1 sK2 sK3 X0
    conv => enter [1]; rw [h41751 X1 sK2 X0 (sK2 ◇ sK3)]
    conv => enter [1, 2, 2]; rw [← l2 sK2 sK3 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41751 X0 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41751 X0 X1 X0 X0]
  have l8 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [h41751 sK1 (sK2 ◇ (sK2 ◇ sK3)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK3)) (X0 ◇ X1)]
  have l9 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = (sK2 ◇ ((sK2 ◇ sK3) ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h41751 sK2 sK3 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK2 sK3 (X0 ◇ X1)]
  have l10 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ sK3) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l9 sK2 sK3 X0 X1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK3) (X0 ◇ X1)]
  have l11 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 sK3 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) (X0 ◇ X1)]
  have l12 : ∀ X1 sK2 : G, (X1 ◇ sK2) = (X1 ◇ X1) := by
    intro X1 sK2
    conv => enter [1]; rw [l6 X1 sK2 X1 X1]
    conv => enter [1]; rw [← l7 X1 ((sK2 ◇ (sK2 ◇ X1)) ◇ X1)]
  have l13 : ∀ X1 sK1 : G, (X1 ◇ sK1) = (X1 ◇ X1) := by
    intro X1 sK1
    conv => enter [1]; rw [l5 X1 sK1 X1 X1 X1]
    conv => enter [1]; rw [← l7 X1 ((sK1 ◇ (sK1 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X1)]
  have l14 : ∀ X4 X0 X1 : G, (X4 ◇ (X0 ◇ X1)) = (X4 ◇ X0) := by
    intro X4 X0 X1
    conv => enter [1]; rw [← l4 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [← h41751 X4 X0 X1 (X4 ◇ X4)]
  have l15 : ∀ X3 X2 : G, (X3 ◇ X2) = (X3 ◇ X3) := by
    intro X3 X2
    conv => enter [1]; rw [l3 X3 X2 X3 X3]
    conv => enter [1]; rw [← l7 X3 ((X3 ◇ X3) ◇ X2)]
  have l16 : ∀ sK2 sK3 : G, (sK2 ◇ sK3) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l10 sK2 sK3 sK2 sK2]
    conv => enter [1, 2]; rw [← l15 sK2 (sK2 ◇ sK3)]
  have l17 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK1 sK1]
    conv => enter [1, 2]; rw [← l15 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l18 : ∀ sK2 sK3 : G, (sK2 ◇ sK3) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK2) := by
    intro sK2 sK3
    conv => enter [1]; rw [l16 sK2 sK3]
    conv => enter [1]; rw [← l12 (sK2 ◇ (sK2 ◇ sK3)) sK2]
  have l19 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l17 sK1 sK2 sK3]
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) sK2]
  have l20 : ∀ sK2 sK3 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l18 sK2 sK3]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ sK3)) sK2]
  have l21 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l19 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) sK2]
  have l22 : ∀ sK2 sK3 : G, (sK2 ◇ sK3) = (sK2 ◇ sK2) := by
    intro sK2 sK3
    conv => enter [1]; rw [l20 sK2 sK3]
    conv => enter [1]; rw [l15 sK2 (sK2 ◇ (sK2 ◇ sK3))]
  have l23 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l21 sK1 sK2 sK3]
    conv => enter [1]; rw [l15 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))))]
  have l24 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK2 ◇ sK1) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l22 sK2 sK3]
    conv => enter [1]; rw [← l13 sK2 sK1]
  have l25 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l23 sK1 sK2 sK3]
    conv => enter [1]; rw [← l13 sK2 sK1]
  have l26 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ sK2) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l24 sK2 sK3 sK1]
    conv => enter [1]; rw [h43 sK2 sK1]
  have l27 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK1 ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l25 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 sK2 sK1]
  have l28 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ sK1) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l26 sK2 sK3 sK1]
    conv => enter [1]; rw [l15 sK1 sK2]
  have l29 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l27 sK1 sK2 sK3]
    conv => enter [1]; rw [l15 sK1 sK2]
  have l30 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l28 sK2 sK3 sK1]
    conv => enter [1]; rw [← l29 sK1 sK2 sK3]
  have l31 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 X0]
    conv => enter [1, 2, 2]; rw [← l30 sK2 sK3 sK1]
  have l32 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ X0) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l31 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l15 sK1 (X0 ◇ (sK2 ◇ sK3))]
  have l33 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1, 2]; rw [← l30 sK2 sK3 sK1]
    conv => enter [1]; rw [l15 sK1 (sK2 ◇ sK3)]
  have l34 : ∀ sK2 sK3 sK1 X0 : G, (sK2 ◇ sK3) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ X0) := by
    intro sK2 sK3 sK1 X0
    conv => enter [1]; rw [l28 sK2 sK3 sK1]
    conv => enter [1]; rw [← l32 sK1 sK2 sK3 X0]
  have l35 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l28 sK2 sK3 sK1]
    conv => enter [1]; rw [← l33 sK1 sK2 sK3]
  have l36 : ∀ sK2 sK3 X0 X1 sK1 : G, (sK2 ◇ sK3) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))))) := by
    intro sK2 sK3 X0 X1 sK1
    conv => enter [1]; rw [l34 sK2 sK3 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))))]
  have l37 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ X1) = (sK2 ◇ sK3) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [← l14 X0 X1 (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))))]
    conv => enter [1]; rw [← l36 sK2 sK3 X0 X1 X0]
  intro x y z w
  conv => enter [1]; rw [l37 x y z w]
  conv => enter [1]; rw [l35 z w x]

end CommutativeSemigroup5
