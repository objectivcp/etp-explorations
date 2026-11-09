import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_41741_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41741 : Equation41741 G) : Equation42237 G := by
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
  have l10 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
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
theorem Equation41741_implies_Equation41737 (G : Type*) [Magma G] (h41741 : Equation41741 G) : Equation41737 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (y ◇ z)))]

theorem Equation43_41741_implies_Equation42225 (G : Type*) [Magma G] (h43 : Equation43 G) (h41741 : Equation41741 G) : Equation42225 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X0 ◇ sK1) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [h43 sK1 X0]
  have l2 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [l2 x w z]
  conv => enter [1]; rw [l0 z (x ◇ w) (z ◇ (z ◇ (x ◇ w)))]

theorem Equation43_4512_41737_implies_Equation38 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l4 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l5 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [h41737 X1 sK0 (X0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l3 sK0 X0 sK1]
  have l6 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [h41737 X1 (sK0 ◇ sK0) (X0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l4 sK0 X0 sK1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l8 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h41737 X0 X1 X2]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
  have l9 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l8 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l10 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41737 X1 X0 (sK0 ◇ (sK0 ◇ X1))]
    conv => enter [1]; rw [← l6 X1 sK0 X0 X1]
  have l11 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41737 X1 X0 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l5 X1 sK0 X0 X1]
  have l12 : ∀ X0 X3 X1 : G, (X0 ◇ X0) = (X3 ◇ (X0 ◇ X1)) := by
    intro X0 X3 X1
    conv => enter [1]; rw [l7 X0 ((X0 ◇ (X1 ◇ X0)) ◇ X3)]
    conv => enter [1]; rw [← l9 X3 X0 X1 X0]
  have l13 : ∀ X0 X3 sK0 : G, (X0 ◇ X0) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 X3 sK0
    conv => enter [1]; rw [l12 X0 X3 X0]
    conv => enter [1]; rw [l10 X3 (X0 ◇ X0) sK0]
  have l14 : ∀ X0 X3 sK0 : G, (X0 ◇ X0) = (X3 ◇ sK0) := by
    intro X0 X3 sK0
    conv => enter [1]; rw [l13 X0 X3 sK0]
    conv => enter [1]; rw [l11 X3 (sK0 ◇ sK0) sK0]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = (sK0 ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l14 X0 X1 sK0]
    conv => enter [1]; rw [h43 X1 sK0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l15 sK0 sK0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation43_4512_41737_implies_Equation41805 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 X0 sK3 : G, (sK2 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l0 sK2 sK3 X0]
  have l2 : ∀ sK2 X0 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 X0 sK3 sK4 sK1 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l3 : ∀ X0 sK3 sK4 sK1 sK0 : G, (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK3 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l0 sK3 (sK4 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ X1 sK2 X0 sK3 sK4 sK1 sK0 : G, (X1 ◇ sK2) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))))) := by
    intro X1 sK2 X0 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h41737 X1 sK2 (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2, 2, 2]; rw [l2 sK2 X0 sK3 sK4 sK1 sK0]
  have l5 : ∀ X1 sK3 X0 sK4 sK1 sK0 : G, (X1 ◇ sK3) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))))) := by
    intro X1 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [h41737 X1 sK3 (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [l3 sK3 X0 sK4 sK1 sK0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0]
    conv => enter [1]; rw [← l7 X0 ((X1 ◇ X0) ◇ X0)]
  have l9 : ∀ X1 X0 sK3 : G, (X1 ◇ X0) = (X1 ◇ sK3) := by
    intro X1 X0 sK3
    conv => enter [1]; rw [h41737 X1 X0 (sK3 ◇ (X1 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [← l5 X1 sK3 X0 X1 X1 X1]
  have l10 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ sK2) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h41737 X1 X0 (sK2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))]
    conv => enter [1]; rw [← l4 X1 sK2 X0 X1 X1 X1 X1]
  have l11 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (sK2 ◇ sK2) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l1 X0 sK2 sK3]
    conv => enter [1]; rw [l8 sK2 (X0 ◇ sK3)]
  have l12 : ∀ sK3 sK4 sK1 sK0 sK2 : G, (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK3 ◇ sK2) := by
    intro sK3 sK4 sK1 sK0 sK2
    conv => enter [1]; rw [l8 sK3 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l10 sK3 sK3 sK2]
  have l13 : ∀ X0 sK3 sK2 : G, (X0 ◇ sK3) = (sK2 ◇ sK2) := by
    intro X0 sK3 sK2
    conv => enter [1]; rw [l9 X0 sK3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l11 X0 sK2 sK3]
  have l14 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h43 sK2 sK3]
    conv => enter [1]; rw [← l12 sK3 sK4 sK1 sK0 sK2]
  have l15 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X0 ◇ sK3) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l8 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l13 X0 sK3 sK2]
  have l16 : ∀ sK3 sK4 sK1 sK0 sK2 : G, (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ sK2) := by
    intro sK3 sK4 sK1 sK0 sK2
    conv => enter [1]; rw [← l14 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l8 sK2 sK3]
  have l17 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X0 ◇ sK2) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l15 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [l10 X0 sK3 sK2]
  have l18 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l8 sK2 sK3]
    conv => enter [1]; rw [← l16 sK3 sK4 sK1 sK0 sK2]
  have l19 : ∀ sK3 sK4 sK1 sK0 sK2 : G, (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK4 sK1 sK0 sK2
    conv => enter [1]; rw [l16 sK3 sK4 sK1 sK0 sK2]
    conv => enter [1]; rw [← l17 sK2 sK3 sK4 sK1 sK0 sK2]
  have l20 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l18 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l19 sK3 sK4 sK1 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l20 x y z w u]

theorem Equation43_4512_41737_implies_Equation41882 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK3 sK4]
    conv => enter [1]; rw [← l3 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  intro x y z w u v
  conv => enter [1]; rw [l4 x y z w u v]

theorem Equation43_4512_41737_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation42405 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l0 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK0) sK1]
  have l2 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [l0 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l3 : ∀ sK3 sK1 sK2 sK0 sK6 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK6 ◇ X0)) = (X0 ◇ (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK3 sK1 sK2 sK0 sK6 X0
    conv => enter [1]; rw [l0 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6 X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
  have l4 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 X0]
  have l5 : ∀ sK1 sK2 sK0 X0 sK3 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK3 X0]
  have l6 : ∀ sK3 sK1 sK2 sK0 X0 sK6 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ sK6)) = (X0 ◇ (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK3 sK1 sK2 sK0 X0 sK6
    conv => enter [1, 2]; rw [h43 X0 sK6]
    conv => enter [1]; rw [l3 sK3 sK1 sK2 sK0 sK6 X0]
  have l7 : ∀ X1 sK2 sK0 X0 sK1 : G, (X1 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro X1 sK2 sK0 X0 sK1
    conv => enter [1]; rw [h41737 X1 (sK2 ◇ sK0) (X0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l4 sK2 sK0 X0 sK1]
  have l8 : ∀ X1 sK1 sK2 sK0 X0 sK3 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))))) := by
    intro X1 sK1 sK2 sK0 X0 sK3
    conv => enter [1]; rw [h41737 X1 (sK1 ◇ (sK2 ◇ sK0)) (X0 ◇ sK3)]
    conv => enter [1, 2, 2, 2]; rw [l5 sK1 sK2 sK0 X0 sK3]
  have l9 : ∀ X1 sK3 sK1 sK2 sK0 X0 sK6 : G, (X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))))))) := by
    intro X1 sK3 sK1 sK2 sK0 X0 sK6
    conv => enter [1]; rw [h41737 X1 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) (X0 ◇ sK6)]
    conv => enter [1, 2, 2, 2]; rw [l6 sK3 sK1 sK2 sK0 X0 sK6]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1 X0]
    conv => enter [1]; rw [← l11 X0 ((X1 ◇ X0) ◇ X0)]
  have l13 : ∀ X1 X0 sK3 sK1 sK2 sK0 : G, (X1 ◇ X0) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X1 X0 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h41737 X1 X0 (X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [← l9 X1 sK3 sK1 sK2 sK0 X0 X1]
  have l14 : ∀ X1 X0 sK1 sK2 sK0 : G, (X1 ◇ X0) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 sK1 sK2 sK0
    conv => enter [1]; rw [h41737 X1 X0 (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l8 X1 sK1 sK2 sK0 X0 X1]
  have l15 : ∀ X1 X0 sK2 sK0 : G, (X1 ◇ X0) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro X1 X0 sK2 sK0
    conv => enter [1]; rw [h41737 X1 X0 (X1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l7 X1 sK2 sK0 X0 X1]
  have l16 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l4 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [l12 (sK2 ◇ sK0) (X0 ◇ sK1)]
  have l17 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l12 (sK2 ◇ sK0) sK1]
  have l18 : ∀ sK6 sK3 sK1 sK2 sK0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l12 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
  have l19 : ∀ sK6 sK3 sK1 sK2 sK0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK6 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l14 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1 sK2 sK0]
  have l20 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK4 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK4 sK5]
    conv => enter [1]; rw [l13 sK4 sK4 sK3 sK1 sK2 sK0]
  have l21 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
    conv => enter [1]; rw [← l16 X0 sK1 sK2 sK0]
  have l22 : ∀ sK6 sK3 sK1 sK2 sK0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK6 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK1 ◇ (sK2 ◇ sK0))]
  have l23 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK4) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK4 sK5 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 sK4 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l24 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l21 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l15 X0 (sK1 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l25 : ∀ sK6 sK3 sK1 sK2 sK0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l22 sK6 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK2 ◇ sK0)) (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l26 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l23 sK4 sK5 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK4]
  have l27 : ∀ sK6 sK3 sK1 sK2 sK0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK6 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l15 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l28 : ∀ sK4 sK5 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK4 sK5 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l14 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1 sK2 sK0]
  have l29 : ∀ sK6 sK3 sK1 sK2 sK0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l27 sK6 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
  have l30 : ∀ sK4 sK5 sK1 sK2 sK0 sK3 : G, (sK4 ◇ sK5) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l28 sK4 sK5 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK1 ◇ (sK2 ◇ sK0))]
  have l31 : ∀ sK6 sK3 sK1 sK2 sK0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l29 sK6 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0))]
  have l32 : ∀ sK4 sK5 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK4 sK5 sK1 sK2 sK0 sK4]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK2 ◇ sK0)) (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l33 : ∀ sK1 sK2 sK0 sK6 sK3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 sK6 sK3
    conv => enter [1]; rw [l24 sK1 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l31 sK6 sK3 sK1 sK2 sK0]
  have l34 : ∀ sK4 sK5 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK5 sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK4 sK5 sK1 sK2 sK0]
    conv => enter [1]; rw [l15 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l35 : ∀ sK4 sK5 sK2 sK0 sK1 : G, (sK4 ◇ sK5) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l34 sK4 sK5 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
  have l36 : ∀ sK4 sK5 sK2 sK0 : G, (sK4 ◇ sK5) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK5 sK2 sK0
    conv => enter [1]; rw [l35 sK4 sK5 sK2 sK0 sK4]
    conv => enter [1]; rw [l12 (sK2 ◇ sK0) (sK4 ◇ (sK2 ◇ sK0))]
  have l37 : ∀ sK4 sK5 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK5 sK1 sK2 sK0
    conv => enter [1]; rw [l36 sK4 sK5 sK2 sK0]
    conv => enter [1]; rw [l24 (sK2 ◇ sK0) sK2 sK0 sK1]
  intro x y z w u v r
  conv => enter [1]; rw [l37 x y u v r]
  conv => enter [1]; rw [l33 u v r z w]

theorem Equation43_4512_41737_implies_Equation41732 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ X0) ◇ X0)]
  intro x y
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [← l3 x (x ◇ (x ◇ (x ◇ x)))]

theorem Equation43_4512_41737_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41737 X1 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l0 X0 sK0 sK0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0]
    conv => enter [1]; rw [← l3 X0 ((X1 ◇ X0) ◇ X0)]
  have l5 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41737 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 X1 sK0 X0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK1 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 sK1 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← l8 z x y]
  conv => enter [1]; rw [← l4 z (z ◇ (z ◇ (z ◇ z)))]

theorem Equation43_4512_41737_implies_Equation41734 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h41737 X0 X1 X0]
    conv => enter [1]; rw [← h41737 X0 X0 (X1 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l3 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l4 x z y]

theorem Equation43_4512_41737_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [h41737 X1 sK0 (X0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l1 sK0 X0 sK1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h41737 X0 X1 X0]
    conv => enter [1]; rw [← h41737 X0 X0 (X1 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [l4 X0 ((X1 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41737 X1 X0 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l2 X1 sK0 X0 X1]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 sK1 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l11 x y z]
  conv => enter [1]; rw [l10 z x]

theorem Equation43_4512_41737_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK2) X0]
  have l2 : ∀ X1 sK1 X0 sK2 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 sK1 X0 sK2
    conv => enter [1]; rw [h41737 X1 sK1 (X0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l1 sK1 X0 sK2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [← l4 X0 ((X1 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 sK1 : G, (X1 ◇ X0) = (X1 ◇ sK1) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h41737 X1 X0 (sK1 ◇ (sK1 ◇ X1))]
    conv => enter [1]; rw [← l2 X1 sK1 X0 X1]
  have l7 : ∀ sK3 sK0 : G, (sK3 ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l5 sK0 sK3]
  have l8 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l1 sK1 X0 sK2]
    conv => enter [1]; rw [l5 sK1 (X0 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l8 X0 sK1 sK2]
  have l10 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l7 sK3 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 sK1]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [l6 X0 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l12 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l10 sK3 sK0 sK1]
    conv => enter [1]; rw [h43 sK0 sK1]
  have l13 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l12 sK3 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1]
    conv => enter [1]; rw [← l13 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [← l14 z w x y]

theorem Equation43_4512_41737_implies_Equation41740 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l3 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l4 x z y]

theorem Equation43_4512_41737_implies_Equation42222 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation42222 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l2 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ sK0) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [h41737 X1 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2, 2, 2]; rw [l1 sK0 X0 sK1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0]
    conv => enter [1]; rw [← l4 X0 ((X1 ◇ X0) ◇ X0)]
  have l6 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41737 X1 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (X1 ◇ X1))))]
    conv => enter [1]; rw [← l2 X1 sK0 X0 X1]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 sK1 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 sK1 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l11 x y z]
  conv => enter [1]; rw [l10 z x]

theorem Equation43_4512_41737_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation42237 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l2 : ∀ X1 sK1 X0 sK2 : G, (X1 ◇ sK1) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))))) := by
    intro X1 sK1 X0 sK2
    conv => enter [1]; rw [h41737 X1 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
    conv => enter [1, 2, 2, 2]; rw [l1 sK1 X0 sK2]
  have l3 : ∀ X1 sK2 X0 : G, (X1 ◇ sK2) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK2))))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h41737 X1 sK2 (X0 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l0 X0 sK2 sK2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0]
    conv => enter [1]; rw [← l5 X0 ((X1 ◇ X0) ◇ X0)]
  have l7 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ sK2) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h41737 X1 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l3 X1 sK2 X0]
  have l8 : ∀ X1 X0 sK1 : G, (X1 ◇ X0) = (X1 ◇ sK1) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h41737 X1 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (X1 ◇ X1))))]
    conv => enter [1]; rw [← l2 X1 sK1 X0 X1]
  have l9 : ∀ sK3 sK0 : G, (sK3 ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l6 sK0 sK3]
  have l10 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (sK1 ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l1 sK1 X0 sK2]
    conv => enter [1]; rw [l6 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l10 X0 sK1 sK2]
  have l12 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = (sK0 ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l9 sK3 sK0]
    conv => enter [1]; rw [l7 sK0 sK0 sK2]
  have l13 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK2 X0]
    conv => enter [1]; rw [l7 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) sK2]
  have l14 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ sK0) = (sK2 ◇ sK0) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l12 sK3 sK0 sK2]
    conv => enter [1]; rw [h43 sK0 sK2]
  have l15 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK2 X0]
    conv => enter [1]; rw [l8 X0 sK2 sK1]
  have l16 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l6 sK2 sK0]
    conv => enter [1]; rw [l14 sK2 sK0 sK3]
  have l17 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← l16 sK2 sK3 sK0]
    conv => enter [1]; rw [l8 sK2 sK2 sK1]
  have l18 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [h43 sK2 sK1]
  have l19 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l18 sK3 sK0 sK1 sK3]
    conv => enter [1]; rw [l6 sK1 sK3]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK1]
    conv => enter [1]; rw [← l19 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [← l20 z w x y]

theorem Equation43_4512_41737_implies_Equation41741 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41737 : Equation41737 G) : Equation41741 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41737 X0 X1 X2]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X2) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41737 X0 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41737 X0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

@[equational_result]
theorem Equation42237_implies_Equation38 (G : Type*) [Magma G] (h42237 : Equation42237 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation43_4512_42237_implies_Equation41805 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42237 : Equation42237 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 sK2 sK3 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK2 ◇ sK3) (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  have l3 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [← l2 sK4 sK4 sK4 sK1 sK0]
    conv => enter [1]; rw [l1 sK4 sK4 sK2 sK3 sK4 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l3 z w u x y]

theorem Equation43_42237_implies_Equation41882 (G : Type*) [Magma G] (h43 : Equation43 G) (h42237 : Equation42237 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 sK5 sK2 sK0 sK1 : G, (X0 ◇ X1) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  have l2 : ∀ sK5 sK2 sK0 sK1 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [← l1 sK5 sK5 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 sK5 sK5 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y z w u v]
  conv => enter [1]; rw [l2 z w u v x]

theorem Equation43_42237_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h42237 : Equation42237 G) : Equation42405 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK4 sK5 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
  intro x y z w u v r
  conv => enter [1]; rw [l1 x y z w u v r]

theorem Equation4512_42237_implies_Equation41732 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42237 : Equation42237 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_42237_implies_Equation42232 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42237 : Equation42237 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation42237_implies_Equation41734 (G : Type*) [Magma G] (h42237 : Equation42237 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

@[equational_result]
theorem Equation42237_implies_Equation42230 (G : Type*) [Magma G] (h42237 : Equation42237 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation43_42237_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h42237 : Equation42237 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ X1) = (sK3 ◇ sK0) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 sK3]
    conv => enter [1]; rw [h43 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l1 x y z (z ◇ (z ◇ (z ◇ w)))]

@[equational_result]
theorem Equation42237_implies_Equation41740 (G : Type*) [Magma G] (h42237 : Equation42237 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l2 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l2 z x y]
  conv => enter [1]; rw [l1 z x]

@[equational_result]
theorem Equation42237_implies_Equation42222 (G : Type*) [Magma G] (h42237 : Equation42237 G) : Equation42222 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42237_implies_Equation41737 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42237 : Equation42237 G) : Equation41737 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42237 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42237 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation42222_implies_Equation38 (G : Type*) [Magma G] (h42222 : Equation42222 G) : Equation38 G := by
  have l0 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42222 sK0 sK0 sK0]
    conv => enter [1]; rw [← h42222 sK0 X1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation42222_implies_Equation41805 (G : Type*) [Magma G] (h42222 : Equation42222 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42222 X0 X1 X0]
    conv => enter [1]; rw [← h42222 X0 X3 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation42222_implies_Equation41882 (G : Type*) [Magma G] (h42222 : Equation42222 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42222 X0 X1 X0]
    conv => enter [1]; rw [← h42222 X0 X3 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_42222_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42222 : Equation42222 G) : Equation42405 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK2 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [h43 (sK2 ◇ sK0) sK1]
  have l2 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l1 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l2 sK1 sK2 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l5 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42222 X0 X1 X0]
    conv => enter [1]; rw [← h42222 X0 X3 X0]
  have l6 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h43 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK2 X0]
  have l7 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK0) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1, 2]; rw [l5 sK2 X0 X1]
    conv => enter [1]; rw [l0 sK0 sK2 X1]
  have l8 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l5 (sK2 ◇ sK0) sK1 X0]
  have l9 : ∀ sK2 sK0 X0 sK1 X1 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK2 sK0 X0 sK1 X1
    conv => enter [1]; rw [l5 (sK2 ◇ sK0) X0 (X1 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 X1]
  have l10 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
  have l11 : ∀ sK1 sK2 sK0 X0 sK3 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro sK1 sK2 sK0 X0 sK3 X1
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ sK0)) X0 (X1 ◇ sK3)]
    conv => enter [1]; rw [← l4 sK3 sK1 sK2 sK0 X1]
  have l12 : ∀ sK6 sK3 sK1 sK2 sK0 X0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK6 sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l5 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6 X0]
  have l13 : ∀ sK6 sK3 sK1 sK2 sK0 X0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK6 sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l12 sK6 sK3 sK1 sK2 sK0 sK6]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0 X0 sK3 sK6]
  have l14 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l10 sK3 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [← l9 sK2 sK0 X0 sK1 sK3]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK2 X0 sK1]
  have l16 : ∀ sK3 sK1 sK2 sK0 sK6 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0 sK6
    conv => enter [1]; rw [l10 sK3 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [← l13 sK6 sK3 sK1 sK2 sK0 sK3]
  have l17 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l8 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l14 sK3 sK1 sK2 sK0 sK1]
  have l18 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l6 sK2 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l15 sK1 sK2 sK0 sK2]
  have l19 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X1) = (sK2 ◇ sK0) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h42222 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK2 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ X0)))]
  have l20 : ∀ sK4 sK5 sK2 sK0 : G, (sK4 ◇ sK5) = (sK2 ◇ sK0) := by
    intro sK4 sK5 sK2 sK0
    conv => enter [1]; rw [l5 sK4 sK5 sK4]
    conv => enter [1]; rw [l19 sK4 sK4 sK2 sK0]
  intro x y z w u v r
  conv => enter [1]; rw [l20 x y v r]
  conv => enter [1]; rw [l18 v r u]
  conv => enter [1]; rw [l17 u v r w]
  conv => enter [1]; rw [l16 w u v r z]

theorem Equation43_4512_42222_implies_Equation41732 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42222 : Equation42222 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h42222 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1]
    conv => enter [1]; rw [h42222 sK0 (X1 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [h42222 (sK0 ◇ sK0) X1 X0]
  have l7 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42222 sK0 sK0 sK0]
    conv => enter [1]; rw [← h42222 sK0 X1 sK0]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1, 2]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 X1 sK0]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42222 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 X1 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l8 x y]
  conv => enter [1]; rw [l11 x]

theorem Equation43_4512_42222_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42222 : Equation42222 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
  have l7 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h42222 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X2))]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42222 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42222 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK0 (X0 ◇ X0)]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h42222 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [h42222 sK0 ((sK0 ◇ sK0) ◇ X1) X0]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l3 sK0 X1]
    conv => enter [1]; rw [h42222 sK0 (X1 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [h42222 (sK0 ◇ sK0) X1 X0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l13 sK0 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X0)]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ X0)]
  have l17 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X1))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l7 X2 X3 X0 X1]
    conv => enter [1]; rw [← l0 X0 (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) (X0 ◇ X1)]
  have l18 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1, 2]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l14 sK0 X1 sK0]
  have l19 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h42222 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 X1 sK0]
  have l20 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [h42222 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 X1 sK0 sK0]
  have l21 : ∀ X2 X3 sK0 X0 : G, (X2 ◇ X3) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X0))) := by
    intro X2 X3 sK0 X0
    conv => enter [1]; rw [l17 X2 X3 X0 X2]
    conv => enter [1]; rw [l15 X0 ((X2 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X2))) ◇ (X0 ◇ X2)) sK0]
  have l22 : ∀ X2 X3 sK0 : G, (X2 ◇ X3) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X2 X3 sK0
    conv => enter [1]; rw [l21 X2 X3 sK0 X2]
    conv => enter [1]; rw [l16 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X2 ◇ X2)) sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0 sK0]
    conv => enter [1]; rw [← l18 sK0 sK0]
  have l24 : ∀ X2 X3 sK0 : G, (X2 ◇ X3) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X2 X3 sK0
    conv => enter [1]; rw [l22 X2 X3 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l25 : ∀ X2 X3 sK0 : G, (X2 ◇ X3) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X3 sK0
    conv => enter [1]; rw [l24 X2 X3 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l26 : ∀ X2 X3 sK0 : G, (X2 ◇ X3) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X2 X3 sK0
    conv => enter [1]; rw [l25 X2 X3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 X2 X3 : G, (sK0 ◇ sK0) = (X2 ◇ X3) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l26 X2 X3 sK0]
  intro x y z
  conv => enter [1]; rw [← l27 z x y]
  conv => enter [1]; rw [l23 z]

@[equational_result]
theorem Equation42222_implies_Equation41734 (G : Type*) [Magma G] (h42222 : Equation42222 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42222 X0 X1 X0]
    conv => enter [1]; rw [← h42222 X0 X3 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation43_4512_42222_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42222 : Equation42222 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42222 X0 X1 X0]
    conv => enter [1]; rw [← h42222 X0 X3 X0]
  have l2 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l1 sK0 X0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l3 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l2 sK0 sK0 X1 sK1]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l3 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_42222_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42222 : Equation42222 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42222 X0 X1 X0]
    conv => enter [1]; rw [← h42222 X0 X3 X0]
  have l2 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l1 sK0 sK3 X0]
  have l3 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ X1) = (sK3 ◇ sK0) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h42222 X0 X1 sK0]
    conv => enter [1]; rw [← l2 sK3 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ X0)))]
  have l4 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [l0 sK1 X0 X1]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ sK1) sK3 sK0]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]
  conv => enter [1]; rw [l1 z w (z ◇ (z ◇ (z ◇ w)))]

theorem Equation43_4512_42222_implies_Equation41740 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42222 : Equation42222 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l7 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h42222 X0 X1 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK1 (X0 ◇ X0)]
  have l8 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h42222 X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X0)]
  have l9 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l1 X1 sK1 sK1]
    conv => enter [1]; rw [h42222 sK1 (X1 ◇ sK1) X0]
  have l10 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l7 X0 X1 sK1]
    conv => enter [1]; rw [l8 sK1 ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) sK1]
  have l11 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [h42222 sK1 sK1 sK1]
    conv => enter [1]; rw [← l9 X1 sK1 sK1]
  have l12 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l10 X0 X1 sK1]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK1) sK1 sK1]
  have l13 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l12 X0 X1 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 (sK1 ◇ sK1) sK1]
  have l14 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ sK1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l13 X0 X1 sK1]
    conv => enter [1]; rw [← h42222 sK1 sK1 sK1]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l11 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l15 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]
  conv => enter [1]; rw [l16 z x]

theorem Equation43_4512_42222_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42222 : Equation42222 G) : Equation42237 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l7 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (sK2 ◇ ((X0 ◇ X0) ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h42222 X0 X1 sK2]
    conv => enter [1, 2]; rw [l1 sK2 sK2 (X0 ◇ X0)]
  have l8 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h42222 X0 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (X0 ◇ X0)]
  have l9 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l1 X1 sK2 sK2]
    conv => enter [1]; rw [h42222 sK2 (X1 ◇ sK2) X0]
  have l10 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK2]
    conv => enter [1]; rw [l8 sK2 ((X0 ◇ X0) ◇ (sK2 ◇ sK2)) sK2]
  have l11 : ∀ sK2 X1 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X1
    conv => enter [1]; rw [h42222 sK2 sK2 sK2]
    conv => enter [1]; rw [← l9 X1 sK2 sK2]
  have l12 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l10 X0 X1 sK2]
    conv => enter [1]; rw [l5 sK2 (sK2 ◇ sK2) sK2 sK2]
  have l13 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l12 X0 X1 sK2]
    conv => enter [1]; rw [l6 sK2 sK2 (sK2 ◇ sK2) sK2]
  have l14 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (sK2 ◇ sK2) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l13 X0 X1 sK2]
    conv => enter [1]; rw [← h42222 sK2 sK2 sK2]
  have l15 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l14 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [l11 sK2 sK1]
  have l16 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l14 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [l15 sK2 sK1]
  have l17 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l14 sK0 sK3 sK2]
    conv => enter [1]; rw [h43 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l17 w x y]
  conv => enter [1]; rw [l16 w z]

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
theorem Equation41740_implies_Equation41805 (G : Type*) [Magma G] (h41740 : Equation41740 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation41740_implies_Equation41882 (G : Type*) [Magma G] (h41740 : Equation41740 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_41740_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41740 : Equation41740 G) : Equation42405 G := by
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
  have l3 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
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
theorem Equation41740_implies_Equation41732 (G : Type*) [Magma G] (h41740 : Equation41740 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (x ◇ x)))]

theorem Equation43_4512_41740_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41740 : Equation41740 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
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
theorem Equation41740_implies_Equation41734 (G : Type*) [Magma G] (h41740 : Equation41740 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (x ◇ z)))]

theorem Equation43_4512_41740_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41740 : Equation41740 G) : Equation42230 G := by
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
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
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

theorem Equation43_4512_41740_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41740 : Equation41740 G) : Equation42233 G := by
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
  have l6 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
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

theorem Equation43_4512_41740_implies_Equation42222 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41740 : Equation41740 G) : Equation42222 G := by
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
  have l4 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41740 X0 X1 X0]
    conv => enter [1]; rw [← h41740 X0 X3 X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 (sK0 ◇ (sK1 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X1]
    conv => enter [1]; rw [l4 sK0 (X1 ◇ (sK1 ◇ sK1)) X0]
  have l7 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ X0) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l4 sK1 X0 (sK2 ◇ X1)]
    conv => enter [1]; rw [l0 sK1 sK2 X1]
  have l8 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l4 (sK1 ◇ sK1) X0 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK2]
  have l9 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK1 X1 sK2]
  have l10 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 X1 sK0]
  have l11 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [l8 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK2]
  have l12 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK2 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 X0 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 z x y]

theorem Equation43_4512_41736_implies_Equation323 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41736 : Equation41736 G) : Equation323 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [h43 (sK0 ◇ sK1) sK0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (X0 ◇ sK0) X1]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l10 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) sK0]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h43 X0 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l9 X2 X0 X1]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [h43 X1 (X0 ◇ X2)]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1 X2]
    conv => enter [1]; rw [h43 X0 (X2 ◇ X1)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [l14 sK0 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK0 (sK0 ◇ sK1) sK1]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l16 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l24 sK0 sK1]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l17 X0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [l15 X0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l31 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l28 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l27 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [l35 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1 (sK0 ◇ sK1)]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l39 x y]

theorem Equation43_4512_41736_implies_Equation41733 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41736 : Equation41736 G) : Equation41733 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l8 sK0 (sK0 ◇ sK1) sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 sK0 (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 sK0 (sK0 ◇ sK1)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 (sK0 ◇ sK1)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK1) sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK1) sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2]; rw [← l24 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l27 x y]
  conv => enter [1]; rw [l25 x y]

theorem Equation43_4512_41736_implies_Equation54318 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41736 : Equation41736 G) : Equation54318 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
    conv => enter [1, 1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ sK0) X1]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l7 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 X1]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0 X1]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l10 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 (sK0 ◇ (sK1 ◇ sK2)) sK0 X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h43 X0 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X0 ◇ X2) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [h43 X1 (X0 ◇ X2)]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41736 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41736 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1, 2, 2]; rw [l14 sK0 sK1 sK2 sK0]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 (sK1 ◇ sK2)]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l26 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l27 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41736 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l22 sK0 sK1 sK2]
  have l29 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l30 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l29 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l28 sK0 sK1 sK2]
  have l32 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l30 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) sK0 sK1 sK2]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
  have l34 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l32 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) (sK0 ◇ (sK1 ◇ sK2))]
  have l35 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l34 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 X0 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l35 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK1 sK2]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l27 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l38 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l39 x y z]

theorem Equation43_4512_41736_implies_Equation53863 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41736 : Equation41736 G) : Equation53863 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l14 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 sK0 (sK0 ◇ sK1)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1))]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1 (sK0 ◇ sK1)]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l29 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l32 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l38 x y]

theorem Equation43_4512_41736_implies_Equation54162 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41736 : Equation41736 G) : Equation54162 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l6 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 (sK0 ◇ sK1)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 sK0 (sK0 ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ sK1)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1, 2]; rw [← l29 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l36 x y]
  conv => enter [1]; rw [l32 x y]
  conv => enter [1]; rw [l29 x y]

theorem Equation43_4512_41736_implies_Equation41529 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41736 : Equation41736 G) : Equation41529 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41736 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x
  conv => enter [1]; rw [l5 x]

theorem Equation43_4512_41736_implies_Equation53860 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41736 : Equation41736 G) : Equation53860 G := by
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
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l5 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1 X0]
    conv => enter [1, 1]; rw [l7 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l16 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l17 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l21 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← l20 (X0 ◇ X1) X3 X2]
  have l22 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ X2)]
  have l23 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l22 X0 X1 X2 X3]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l23 X0 X1 X2 X3]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l15 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41736 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2, 2]; rw [l11 sK0 sK1 sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l19 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ sK1)]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l19 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 sK0 (sK0 ◇ sK1)]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2]; rw [l19 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) sK1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1, 2]; rw [l19 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1, 2]; rw [l15 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l9 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l7 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1, 2]; rw [l24 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l7 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  intro x y
  conv => enter [1, 2]; rw [l44 x y]

theorem Equation43_4512_41736_implies_Equation53807 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41736 : Equation41736 G) : Equation53807 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l2 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l10 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l9 X2 X0 X1]
  have l16 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l17 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
  have l20 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← l14 (X0 ◇ X1) X3 X2]
  have l21 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ X2)]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
  have l23 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l22 X0 X1 X2 X3]
  have l24 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h41736 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l5 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41736 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ X0)))]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (X0 ◇ X0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (X0 ◇ X0)) (sK0 ◇ sK0)]
  have l27 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41736 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (X0 ◇ X0)) (sK0 ◇ sK0)]
  have l30 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)))]
  have l31 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0) sK0 (X0 ◇ X0)]
  have l33 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l34 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X0))]
  have l36 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l15 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [← l3 sK0 (X0 ◇ X0)]
  have l38 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [l23 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l37 sK0 X0]
  have l40 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [l19 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l41 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [l40 sK0]
    conv => enter [1]; rw [l5 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l42 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1, 2]; rw [← l39 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l43 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l44 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l43 sK0]
  have l45 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l34 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l47 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l34 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l48 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l34 sK0]
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l49 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l48 sK0]
    conv => enter [1]; rw [← l44 sK0]
  have l50 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l47 sK0]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0))]
  have l51 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [← l49 sK0]
  have l52 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l50 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l53 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l52 sK0]
  have l54 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [l53 sK0]
  have l55 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l51 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l56 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l44 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l57 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l54 sK0]
    conv => enter [1]; rw [← l56 sK0]
  have l58 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l57 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l59 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l58 sK0]
    conv => enter [1]; rw [← l46 sK0]
  intro x
  conv => enter [1]; rw [← l59 x]
  conv => enter [1]; rw [l55 x]

@[equational_result]
theorem Equation42233_implies_Equation38 (G : Type*) [Magma G] (h42233 : Equation42233 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation43_4512_42233_implies_Equation41805 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42233 : Equation42233 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 sK2 sK3 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK2 ◇ sK3) (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  have l3 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [← l2 sK4 sK4 sK4 sK1 sK0]
    conv => enter [1]; rw [l1 sK4 sK4 sK2 sK3 sK4 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l3 z w u x y]

theorem Equation43_42233_implies_Equation41882 (G : Type*) [Magma G] (h43 : Equation43 G) (h42233 : Equation42233 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 sK5 sK2 sK0 sK1 : G, (X0 ◇ X1) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  have l2 : ∀ sK5 sK2 sK0 sK1 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [← l1 sK5 sK5 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 sK5 sK5 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y z w u v]
  conv => enter [1]; rw [l2 z w u v x]

theorem Equation43_42233_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h42233 : Equation42233 G) : Equation42405 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK4 sK5 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
  intro x y z w u v r
  conv => enter [1]; rw [l1 x y z w u v r]

theorem Equation4512_42233_implies_Equation41732 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42233 : Equation42233 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_42233_implies_Equation42232 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42233 : Equation42233 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation42233_implies_Equation41734 (G : Type*) [Magma G] (h42233 : Equation42233 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

@[equational_result]
theorem Equation42233_implies_Equation42230 (G : Type*) [Magma G] (h42233 : Equation42233 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation42233_implies_Equation41740 (G : Type*) [Magma G] (h42233 : Equation42233 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ X1) = (X4 ◇ X5) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h42233 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42233 X4 X5 X0 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l2 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l2 z x y]
  conv => enter [1]; rw [l1 z x]

@[equational_result]
theorem Equation42230_implies_Equation38 (G : Type*) [Magma G] (h42230 : Equation42230 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42230 X0 X1 X0]
    conv => enter [1]; rw [← h42230 X0 X3 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation42230_implies_Equation41805 (G : Type*) [Magma G] (h42230 : Equation42230 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42230 X0 X1 X0]
    conv => enter [1]; rw [← h42230 X0 X3 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation42230_implies_Equation41882 (G : Type*) [Magma G] (h42230 : Equation42230 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42230 X0 X1 X0]
    conv => enter [1]; rw [← h42230 X0 X3 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_42230_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42230 : Equation42230 G) : Equation42405 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK2 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [h43 (sK2 ◇ sK0) sK1]
  have l2 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l1 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l2 sK1 sK2 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l5 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42230 X0 X1 X0]
    conv => enter [1]; rw [← h42230 X0 X3 X0]
  have l6 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h43 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK2 X0]
  have l7 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK0) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1, 2]; rw [l5 sK2 X0 X1]
    conv => enter [1]; rw [l0 sK0 sK2 X1]
  have l8 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l5 (sK2 ◇ sK0) sK1 X0]
  have l9 : ∀ sK2 sK0 X0 sK1 X1 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK2 sK0 X0 sK1 X1
    conv => enter [1]; rw [l5 (sK2 ◇ sK0) X0 (X1 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 X1]
  have l10 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
  have l11 : ∀ sK1 sK2 sK0 X0 sK3 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro sK1 sK2 sK0 X0 sK3 X1
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ sK0)) X0 (X1 ◇ sK3)]
    conv => enter [1]; rw [← l4 sK3 sK1 sK2 sK0 X1]
  have l12 : ∀ sK6 sK3 sK1 sK2 sK0 X0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK6 sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l5 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6 X0]
  have l13 : ∀ sK6 sK3 sK1 sK2 sK0 X0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK6 sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l12 sK6 sK3 sK1 sK2 sK0 sK6]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0 X0 sK3 sK6]
  have l14 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l10 sK3 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [← l9 sK2 sK0 X0 sK1 sK3]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK2 X0 sK1]
  have l16 : ∀ sK3 sK1 sK2 sK0 sK6 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0 sK6
    conv => enter [1]; rw [l10 sK3 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [← l13 sK6 sK3 sK1 sK2 sK0 sK3]
  have l17 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l8 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l14 sK3 sK1 sK2 sK0 sK1]
  have l18 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l6 sK2 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l15 sK1 sK2 sK0 sK2]
  have l19 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X1) = (sK2 ◇ sK0) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h42230 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK2 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ X0)))]
  have l20 : ∀ sK4 sK5 sK2 sK0 : G, (sK4 ◇ sK5) = (sK2 ◇ sK0) := by
    intro sK4 sK5 sK2 sK0
    conv => enter [1]; rw [l5 sK4 sK5 sK4]
    conv => enter [1]; rw [l19 sK4 sK4 sK2 sK0]
  intro x y z w u v r
  conv => enter [1]; rw [l20 x y v r]
  conv => enter [1]; rw [l18 v r u]
  conv => enter [1]; rw [l17 u v r w]
  conv => enter [1]; rw [l16 w u v r z]

@[equational_result]
theorem Equation42230_implies_Equation41732 (G : Type*) [Magma G] (h42230 : Equation42230 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h42230 X0 X1 X0]
    conv => enter [1]; rw [← h42230 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (x ◇ x)))]

theorem Equation43_4512_42230_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42230 : Equation42230 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42230 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42230 X0 X1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0 (sK0 ◇ X0)]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ X0)]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [l7 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ X0) sK0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l11 X0 X1 sK0]
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l12 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l13 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation43_4512_42230_implies_Equation41734 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42230 : Equation42230 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l4 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h42230 sK1 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1 sK0 sK0]
  have l5 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l4 sK1 X0 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK0]
  have l6 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l5 sK1 X0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK1 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l6 sK1 X0 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h42230 X0 X1 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))]
  intro x y z
  conv => enter [1]; rw [l9 x y x z]

theorem Equation43_4512_42230_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42230 : Equation42230 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ ((X0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (X0 ◇ (sK1 ◇ sK2)) X1]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK2) X1]
  have l8 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l7 sK1 sK2 X0 X1]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = (sK1 ◇ ((X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l3 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X1]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK2)) X1]
  have l11 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0 X1]
    conv => enter [1]; rw [l10 sK1 sK2 X0 X1]
  have l12 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l13 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
  have l16 : ∀ sK2 X0 X1 sK1 : G, ((sK2 ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [h42230 (sK2 ◇ X0) X1 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l17 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h42230 sK2 X0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK2 sK1 sK1]
  have l18 : ∀ sK2 X0 X1 sK1 : G, ((sK2 ◇ X0) ◇ X1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0))) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l16 sK2 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK1 X0]
  have l19 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l17 sK2 X0 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK1]
  have l20 : ∀ sK2 X0 X1 sK1 : G, ((sK2 ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l18 sK2 X0 X1 sK1]
    conv => enter [1]; rw [l15 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK1 X0]
  have l21 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l19 sK2 X0 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l22 : ∀ sK2 X0 X1 sK1 : G, ((sK2 ◇ X0) ◇ X1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ X0)) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l20 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← l11 sK1 sK2 sK1 X0]
  have l23 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK1) = (sK2 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← l21 sK2 X0 sK1]
  have l24 : ∀ sK2 X0 X1 sK1 : G, ((sK2 ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l22 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← l1 sK1 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l25 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l23 sK1 sK2 X0]
  have l26 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK2 ◇ X0) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [← l24 sK2 X0 X1 sK1]
  have l27 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK2 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l26 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK2 X0 X1]
  have l28 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK2 (X0 ◇ sK1)]
    conv => enter [1]; rw [← l27 sK1 sK2 X0 sK1]
  have l29 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42230 X0 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [← l28 sK1 sK2 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)))]
  have l30 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l29 sK0 sK3 sK1 sK2]
    conv => enter [1]; rw [h43 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l30 z w x y]

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
theorem Equation41734_implies_Equation41805 (G : Type*) [Magma G] (h41734 : Equation41734 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41734 X0 X1 X0]
    conv => enter [1]; rw [← h41734 X0 X3 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation41734_implies_Equation41882 (G : Type*) [Magma G] (h41734 : Equation41734 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41734 X0 X1 X0]
    conv => enter [1]; rw [← h41734 X0 X3 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_41734_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41734 : Equation41734 G) : Equation42405 G := by
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
  have l3 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41734 X0 X1 X0]
    conv => enter [1]; rw [← h41734 X0 X3 X0]
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
theorem Equation41734_implies_Equation41732 (G : Type*) [Magma G] (h41734 : Equation41734 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41734 X0 X1 X0]
    conv => enter [1]; rw [← h41734 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (x ◇ x)))]

theorem Equation43_4512_41734_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41734 : Equation41734 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41734 X0 X1 X0]
    conv => enter [1]; rw [← h41734 X0 X3 X0]
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

theorem Equation43_4512_41734_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41734 : Equation41734 G) : Equation42230 G := by
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
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = (X0 ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41734 X0 X1 X0]
    conv => enter [1]; rw [← h41734 X0 X3 X0]
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
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1]; rw [← l12 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l13 z x y]

theorem Equation43_4512_41733_implies_Equation41529 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41733 : Equation41733 G) : Equation41529 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41733 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x
  conv => enter [1]; rw [l5 x]

@[equational_result]
theorem Equation42232_implies_Equation38 (G : Type*) [Magma G] (h42232 : Equation42232 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h42232 X0 X1 X0]
    conv => enter [1]; rw [← h42232 X3 X4 X0]
  intro x y
  conv => enter [1]; rw [l0 x x x y]

theorem Equation43_4512_42232_implies_Equation41805 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42232 : Equation42232 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h42232 X0 X1 X0]
    conv => enter [1]; rw [← h42232 X3 X4 X0]
  have l1 : ∀ X0 X1 sK2 sK3 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK2 ◇ sK3) (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ X1) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  have l3 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [← l2 sK4 sK4 sK4 sK1 sK0]
    conv => enter [1]; rw [l1 sK4 sK4 sK2 sK3 sK4 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) sK4]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l3 z w u x y]

theorem Equation43_42232_implies_Equation41882 (G : Type*) [Magma G] (h43 : Equation43 G) (h42232 : Equation42232 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h42232 X0 X1 X0]
    conv => enter [1]; rw [← h42232 X3 X4 X0]
  have l1 : ∀ X0 X1 sK5 sK2 sK0 sK1 : G, (X0 ◇ X1) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  have l2 : ∀ sK5 sK2 sK0 sK1 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [← l1 sK5 sK5 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 sK5 sK5 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ sK4) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK3 sK4 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y z w u v]
  conv => enter [1]; rw [l2 z w u v x]

theorem Equation43_42232_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h42232 : Equation42232 G) : Equation42405 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h42232 X0 X1 X0]
    conv => enter [1]; rw [← h42232 X3 X4 X0]
  have l1 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK4 sK5 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
  intro x y z w u v r
  conv => enter [1]; rw [l1 x y z w u v r]

theorem Equation4512_42232_implies_Equation41732 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42232 : Equation42232 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h42232 X0 X1 X0]
    conv => enter [1]; rw [← h42232 X3 X4 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation42232_implies_Equation41734 (G : Type*) [Magma G] (h42232 : Equation42232 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ X1) = (X3 ◇ X4) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h42232 X0 X1 X0]
    conv => enter [1]; rw [← h42232 X3 X4 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

@[equational_result]
theorem Equation41732_implies_Equation38 (G : Type*) [Magma G] (h41732 : Equation41732 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41732 X0 X1]
    conv => enter [1]; rw [← h41732 X0 X2]
  intro x y
  conv => enter [1]; rw [l0 x x y]

@[equational_result]
theorem Equation41732_implies_Equation41805 (G : Type*) [Magma G] (h41732 : Equation41732 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41732 X0 X1]
    conv => enter [1]; rw [← h41732 X0 X2]
  intro x y z w u
  conv => enter [1]; rw [l0 x y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation41732_implies_Equation41882 (G : Type*) [Magma G] (h41732 : Equation41732 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41732 X0 X1]
    conv => enter [1]; rw [← h41732 X0 X2]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_41732_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41732 : Equation41732 G) : Equation42405 G := by
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
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41732 X0 X1]
    conv => enter [1]; rw [← h41732 X0 X2]
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

theorem Equation43_4512_41732_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41732 : Equation41732 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41732 X0 X1]
    conv => enter [1]; rw [← h41732 X0 X2]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h41732 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l5 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l8 X0 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l9 X0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK2]
  intro x y z
  conv => enter [1]; rw [← l13 z x y]

theorem Equation43_4512_54646_implies_Equation4271 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54646 : Equation54646 G) : Equation4271 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h43 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l5 : ∀ X0 X1 X2 X6 X7 X8 : G, (X0 ◇ (X1 ◇ X2)) = (X6 ◇ (X7 ◇ X8)) := by
    intro X0 X1 X2 X6 X7 X8
    conv => enter [1]; rw [h54646 X0 X1 X2 X0 X0 X0]
    conv => enter [1]; rw [← h54646 X6 X7 X8 X0 X0 X0]
  have l6 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0 X3 sK0]
    conv => enter [1]; rw [l0 sK0 X3 sK0]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l6 sK0 X1 sK0 X0 sK0]
    conv => enter [1]; rw [l0 sK0 X1 sK0]
  have l8 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [← l6 sK1 X1 sK2 X0 sK0]
    conv => enter [1]; rw [l4 sK1 X1 sK2]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [l7 X0 sK0 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l9 sK0 X0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l12 x y z]

theorem Equation43_4512_54646_implies_Equation54340 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54646 : Equation54646 G) : Equation54340 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h43 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l0 X0 (sK1 ◇ (sK2 ◇ sK3)) sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l0 X0 sK1 (sK2 ◇ sK3)]
  have l5 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l0 X0 sK2 sK3]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l6 : ∀ X0 X1 X2 X6 X7 X8 : G, (X0 ◇ (X1 ◇ X2)) = (X6 ◇ (X7 ◇ X8)) := by
    intro X0 X1 X2 X6 X7 X8
    conv => enter [1]; rw [h54646 X0 X1 X2 X0 X0 X0]
    conv => enter [1]; rw [← h54646 X6 X7 X8 X0 X0 X0]
  have l7 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1, 2]; rw [h43 X0 sK0]
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 X0]
  have l8 : ∀ X0 X1 X2 sK1 sK2 sK3 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ X3) := by
    intro X0 X1 X2 sK1 sK2 sK3 X3
    conv => enter [1]; rw [l6 X0 X1 X2 sK1 X3 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 X3]
  have l9 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [← l8 sK1 X1 (sK2 ◇ sK3) sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l4 sK1 X1 sK2 sK3]
  have l10 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (X1 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [← l8 sK2 X1 sK3 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l5 sK2 X1 sK3]
  have l11 : ∀ X0 sK1 sK2 sK3 X1 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 X1 sK0
    conv => enter [1]; rw [← l9 sK1 sK2 sK3 (X1 ◇ sK0) X0]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 X1 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0 X0]
  have l13 : ∀ sK1 sK2 sK3 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X1
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l11 sK1 sK1 sK2 sK3 X1 sK0]
  have l14 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK2 sK3 sK0 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l10 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  intro x y z w
  conv => enter [1]; rw [← l14 x y z w x]

end CommutativeSemigroup5
