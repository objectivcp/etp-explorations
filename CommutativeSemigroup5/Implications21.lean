import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_41559_implies_Equation41543 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41559 : Equation41559 G) : Equation41543 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 sK0 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK2 ◇ (sK3 ◇ sK0))]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l0 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41559 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41559 X0 X0 X1]
  have l6 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1, 2]; rw [h41559 (sK2 ◇ (sK3 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1, 2]; rw [h41559 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41559 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) sK1 sK1]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41559 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK1 sK1]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 (sK1 ◇ (sK1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1, 2]; rw [← l10 sK1 X0 X0 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l0 X1 X1 X0]
  have l15 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l4 sK1 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l13 (sK2 ◇ (sK3 ◇ sK0)) sK1]
  have l16 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l15 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l0 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK1)]
  have l17 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l14 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l16 sK2 sK3 sK0 sK1]
  have l18 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l17 sK2 sK3 sK0 sK1]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l13 (sK2 ◇ (sK3 ◇ sK0)) sK1]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK1)]
  have l21 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l21 x y z w]

theorem Equation43_4512_41559_implies_Equation41558 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41559 : Equation41559 G) : Equation41558 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l6 X0 X1 X2 X3]
  have l8 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h41559 X1 sK1 (X0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41559 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41559 X0 X0 X1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41559 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0))]
  have l11 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h41559 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l3 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l12 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h41559 (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l13 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1 sK1 sK1]
  have l14 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l11 sK1 sK1 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l16 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l8 X1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l13 sK1]
  have l18 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l9 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l14 sK1]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [l7 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l20 : ∀ X1 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l16 X1 sK1 X0]
    conv => enter [1, 2]; rw [← l3 sK1 X0]
  have l21 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l18 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1]; rw [l7 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l23 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1]; rw [← l21 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1 sK0]
    conv => enter [1]; rw [← l20 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l23 sK1]
    conv => enter [1, 2]; rw [l25 sK1 sK0]
  have l27 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l17 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l28 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l27 X0 sK1]
    conv => enter [1]; rw [← l20 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 X0]
  have l29 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1]; rw [← l28 X0 sK1]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK0]
    conv => enter [1]; rw [← l26 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l31 x y]

theorem Equation43_4512_41559_implies_Equation41562 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41559 : Equation41559 G) : Equation41562 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
  have l4 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l5 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK2) X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41559 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41559 X0 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41559 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l8 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [h41559 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [h41559 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l10 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41559 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1 sK1]
    conv => enter [1]; rw [← l9 sK1 sK2 sK1 sK1]
  have l11 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l8 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41559 (sK2 ◇ sK2) sK2 sK2]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41559 (sK0 ◇ sK0) sK0 sK0]
  have l13 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← l6 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l14 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l6 sK2 sK2]
    conv => enter [1]; rw [l11 sK2]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l14 sK2]
    conv => enter [1]; rw [l5 sK1 (sK2 ◇ sK2) sK2]
  have l17 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 sK2
    conv => enter [1, 2]; rw [l14 sK2]
    conv => enter [1]; rw [← l0 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l16 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
  have l19 : ∀ X0 sK2 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h41559 X0 (sK2 ◇ sK2) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [← l16 sK1 sK2]
  have l20 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l19 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← l17 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l21 : ∀ X0 sK2 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l20 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l22 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l21 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 sK2]
  have l23 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [l4 sK0 (sK2 ◇ sK2) sK1 sK2]
  have l25 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h41559 X0 (sK2 ◇ sK2) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK0 sK1 sK2]
  have l26 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l25 X0 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l17 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) sK2]
  have l27 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l26 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) (sK2 ◇ sK2)]
  have l28 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l27 X0 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l24 sK0 sK1 sK2]
  have l29 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l13 sK1 sK2]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l29 sK1 sK2 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [← l28 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0 sK1 sK2]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1 sK2]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK1 ◇ (sK2 ◇ sK2))]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ (sK2 ◇ sK2)) sK1 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l28 (sK1 ◇ (sK2 ◇ sK2)) sK0 sK1 sK2]
  have l36 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [← l35 sK0 sK1 sK2]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l36 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l37 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l38 x y z]

theorem Equation43_4512_41558_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41558 : Equation41558 G) : Equation308 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK0 ◇ sK1)]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK1)]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l11 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l13 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
  have l16 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l19 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l12 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l20 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l19 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l21 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
  have l23 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X1) ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← l17 (X0 ◇ X1) X3 X2]
  have l24 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l23 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ X2)]
  have l25 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l24 X0 X1 X2 X3]
  have l26 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l25 X0 X1 X2 X3]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41558 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41558 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41558 sK1 X0]
    conv => enter [1]; rw [← l4 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41558 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l6 sK0 sK1 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l31 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41558 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41558 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l29 sK0 sK1 sK0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ sK0) sK0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l15 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l40 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l35 sK0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l15 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l15 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l45 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l40 sK0]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [l16 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [l18 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [l15 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1]
    conv => enter [1]; rw [l48 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l42 sK0 sK1]
  have l52 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l46 sK0 sK0]
    conv => enter [1]; rw [← l51 sK0 sK0]
  have l53 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l52 sK0]
    conv => enter [1]; rw [← l17 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l54 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41558 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l42 sK0 sK1]
  have l55 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l17 (sK0 ◇ (sK0 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l56 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l55 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l57 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l54 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l15 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l58 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l57 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l56 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l59 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l58 X0 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l42 sK0 sK1]
  have l60 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l59 X0 sK0 X0]
    conv => enter [1, 2]; rw [← l46 sK0 X0]
  have l61 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← l45 sK0]
  have l62 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l61 sK0 X0]
  have l63 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l53 sK0 X0]
    conv => enter [1]; rw [← l62 sK0 X0]
  have l64 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l60 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [l0 X0 X1 (X0 ◇ X1)]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l60 sK1 sK0]
  have l66 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [← l60 X0 sK0]
  have l67 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l60 X0 sK0]
  have l68 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l67 X0 sK0 X1]
  have l69 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l63 sK0 X0]
    conv => enter [1]; rw [l66 sK0 X0]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK1 (sK0 ◇ sK0)]
  have l71 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1]; rw [l64 X0 X1 sK0]
  have l72 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ sK0)]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l74 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l60 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l75 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41558 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2, 2]; rw [← l44 sK0 sK1]
  have l76 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l75 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l15 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l78 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l76 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l71 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l79 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l60 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l77 sK0 sK1]
  have l80 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l78 X0 sK0 sK1]
    conv => enter [1]; rw [l26 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l79 sK0 sK1]
  have l82 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l80 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l81 sK0 sK1]
  have l84 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l82 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l69 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l85 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l84 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l83 sK0 sK1]
  have l86 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l73 sK0 sK1]
  have l87 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 sK1]
    conv => enter [1]; rw [← l68 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l88 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l85 sK0 sK0 sK1]
    conv => enter [1]; rw [← l87 sK0 sK1]
  have l89 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1]
    conv => enter [1]; rw [← l50 sK0 sK1]
  have l90 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l89 sK0 sK1]
    conv => enter [1]; rw [l60 (sK0 ◇ sK1) sK0]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l90 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l92 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l92 sK0 sK1]
    conv => enter [1]; rw [← l93 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l94 x y]

theorem Equation43_4512_41558_implies_Equation41530 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41558 : Equation41558 G) : Equation41530 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l7 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l12 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l12 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l11 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l11 sK0 sK1]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l17 sK0 sK1]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK1))]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l20 sK0 sK1 X0]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l22 sK0 sK1 X0]
  have l24 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41558 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [l17 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41558 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41558 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41558 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41558 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41558 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ sK1) sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l35 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l24 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l19 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1, 2]; rw [h43 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l41 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l35 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l46 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l41 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l50 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l46 X0 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l42 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ sK1))]
  have l53 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l50 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l19 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l56 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l53 X0 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l42 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l42 sK0 sK1]
  have l58 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l56 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l16 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l60 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l58 X0 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l42 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l42 sK0 sK1]
  have l62 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l60 X0 sK0 X0]
    conv => enter [1, 2]; rw [← l55 sK0 X0]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1, 2]; rw [l19 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l62 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK0]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK0)]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ sK1)]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1, 2]; rw [l62 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK0]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK0)]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l73 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [l62 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK0]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK0)]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK0]
    conv => enter [1]; rw [l76 sK0 sK1]
  have l78 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l38 sK0 sK1]
  have l79 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l79 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l81 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l62 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l80 sK0 sK1]
  have l82 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l81 sK0 sK1]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l82 sK0 sK1]
  have l84 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 (sK0 ◇ sK1)]
  have l85 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ sK1)]
  have l86 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l85 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l87 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1)]
  have l88 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l87 sK0 sK1]
  have l89 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l86 sK0 sK1]
  have l90 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [← l89 sK0 sK1]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l90 sK0 sK1]
    conv => enter [1]; rw [l62 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l92 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK0)]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l92 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ sK1)]
  have l95 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1)]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1]
    conv => enter [1]; rw [← l95 sK0 sK1]
  have l97 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l96 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l98 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l97 sK0 sK1]
    conv => enter [1]; rw [l62 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l99 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l98 sK0 sK1]
  have l100 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l93 sK0 sK1]
    conv => enter [1]; rw [← l99 sK0 sK1]
  have l101 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l100 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l101 x y]

theorem Equation43_4512_41558_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41558 : Equation41558 G) : Equation41532 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l5 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l13 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l14 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41558 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h41558 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41558 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l21 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1 sK1]
    conv => enter [1]; rw [← h41558 (sK1 ◇ sK1) sK1]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ sK0) sK0]
  have l23 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41558 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41558 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l26 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l21 sK1]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l29 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l26 sK1]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l27 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK1 ◇ sK1)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1)]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l29 sK1]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l29 sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK1]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 (sK0 ◇ sK0)]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l40 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l42 sK1 sK0]
  have l44 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0) X0]
  have l45 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l44 sK0 X0 sK1]
    conv => enter [1]; rw [← l1 sK1 X0 (sK0 ◇ sK0)]
  have l46 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41558 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l30 sK0]
  have l47 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l46 X0 sK0]
    conv => enter [1, 2]; rw [l16 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l48 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l47 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l24 (sK0 ◇ sK0) sK0]
  have l49 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l48 X0 sK0]
    conv => enter [1, 2]; rw [← l24 sK0 sK0]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l38 sK1 sK0]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l51 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1)]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l53 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l54 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK0]
    conv => enter [1]; rw [← l55 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l56 x y]

theorem Equation43_4512_41558_implies_Equation41533 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41558 : Equation41558 G) : Equation41533 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
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
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41558 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l17 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l18 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41558 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2 sK0]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK0]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l24 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41558 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l17 sK1 sK2 sK1]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ sK0) sK0]
  have l26 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41558 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  have l30 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l31 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l25 sK0]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l31 sK0]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
  have l37 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l34 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l38 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
  have l39 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l30 sK1 sK2]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 sK2]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l30 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK2]
  have l41 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l39 sK0 sK1 sK2]
  have l43 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
  have l44 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l42 sK0 sK1 sK2]
  have l45 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l37 sK1 sK2 sK0]
    conv => enter [1]; rw [l44 sK1 sK2 sK0]
  have l46 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41558 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l35 sK0]
  have l47 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l46 X0 sK0]
    conv => enter [1, 2]; rw [l15 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l48 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l47 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l26 (sK0 ◇ sK0) sK0]
  have l49 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l48 X0 sK0]
    conv => enter [1, 2]; rw [← l26 sK0 sK0]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l37 sK1 sK2 sK0]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l50 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l49 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1]; rw [← l27 sK0 sK1 sK2]
  have l54 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l49 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
  have l55 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
  have l56 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l54 sK0 sK1 sK2]
  have l57 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l56 sK0 sK1 sK2]
  have l59 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
  have l60 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l58 sK0 sK1 sK2]
    conv => enter [1]; rw [← l59 sK0 sK1 sK2]
  have l61 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l62 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l60 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 (sK0 ◇ sK0)]
  have l63 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l62 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ sK0)]
  have l64 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l61 sK0 sK1 sK2]
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
  have l65 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l64 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l66 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l65 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l67 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [← l38 sK1 sK2 sK0]
  have l68 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l67 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l58 sK0 sK1 sK2]
  have l69 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l43 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2]
  have l70 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l45 sK1 sK2 sK0]
    conv => enter [1]; rw [← l69 sK0 sK1 sK2]
  have l71 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l70 sK1 sK2 sK0]
  have l72 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l49 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [l71 sK0 sK1 sK2]
  have l73 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l72 sK0 sK1 sK2]
  have l74 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l73 sK0 sK1 sK2]
  have l75 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l74 sK0 sK1 sK2]
  have l76 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l64 sK0 sK1 sK2]
    conv => enter [1]; rw [← l75 sK0 sK1 sK2]
  have l77 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l76 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
  have l78 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l1 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l49 X0 sK0]
  have l79 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41558 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2, 2, 2]; rw [← l33 sK0 sK1 sK2]
  have l80 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l79 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l15 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l81 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l80 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l68 sK0 sK1 sK2 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l82 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l81 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l83 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l82 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l78 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l84 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l83 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l78 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l85 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l84 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l66 sK0 sK1 sK2 (sK0 ◇ sK0)]
  have l86 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l85 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ sK0)]
  have l87 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l86 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l64 sK0 sK1 sK2]
  have l88 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
    conv => enter [1]; rw [← l87 (sK0 ◇ sK0) sK0 sK1 sK2]
  have l89 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [← l88 sK0 sK1 sK2]
  have l90 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l89 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
  have l91 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l77 sK0 sK1 sK2]
    conv => enter [1]; rw [← l90 sK0 sK1 sK2]
  have l92 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 sK0]
    conv => enter [1]; rw [← l91 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l92 x y z]

theorem Equation43_4512_41558_implies_Equation41539 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41558 : Equation41558 G) : Equation41539 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l10 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ sK2))]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 (sK1 ◇ sK2)]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l14 sK1 sK2]
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
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41558 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l21 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l22 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK0]
  have l27 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41558 (sK1 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l22 sK1 sK2 sK1]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l21 sK1 sK2 sK1]
    conv => enter [1]; rw [← h41558 (sK1 ◇ sK2) sK1]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ sK0) sK0]
  have l30 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41558 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l33 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l34 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l28 sK1 sK2]
  have l35 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l29 sK0]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l37 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
  have l38 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l39 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l35 sK0]
  have l40 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l36 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2))]
  have l41 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l34 sK1 sK2]
  have l42 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l41 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l43 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l42 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l44 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l38 sK1 sK2]
  have l45 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l46 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l45 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
  have l47 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41558 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l39 sK0]
  have l48 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l39 sK0]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l48 sK0 X0]
  have l50 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l47 X0 sK0]
    conv => enter [1, 2]; rw [l19 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l51 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l50 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l30 (sK0 ◇ sK0) sK0]
  have l52 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l51 X0 sK0]
    conv => enter [1, 2]; rw [← l30 sK0 sK0]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [l40 sK1 sK2 sK0]
  have l54 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [l40 sK1 sK2 sK0]
  have l55 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [l40 sK1 sK2 sK0]
  have l56 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l55 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l57 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l54 sK0 sK1 sK2]
  have l58 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l53 sK0 sK1 sK2]
  have l59 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l52 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
  have l60 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l58 sK0 sK1 sK2]
    conv => enter [1]; rw [l52 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK0]
  have l61 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
  have l62 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ sK0)]
  have l63 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l61 sK0 sK1 sK2]
  have l64 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [l62 sK0 sK1 sK2]
  have l65 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
    conv => enter [1]; rw [l64 sK0 sK1 sK2]
  have l66 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l68 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l67 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
  have l69 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l66 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l70 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l68 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l52 (sK1 ◇ sK2) sK0]
  have l71 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l69 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l52 (sK1 ◇ sK2) sK0]
  have l72 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l70 sK1 sK2 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ sK2)]
  have l73 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l71 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l74 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l73 sK1 sK2 sK0]
    conv => enter [1]; rw [← l49 sK0 (sK1 ◇ sK2)]
  have l75 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l72 sK1 sK2 sK0]
    conv => enter [1]; rw [← l74 sK1 sK2 sK0]
  have l76 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l46 sK1 sK2 sK0]
  have l77 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [l46 sK1 sK2 sK0]
  have l78 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l77 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l79 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l76 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l80 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l79 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l81 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l80 sK0 sK1 sK2]
    conv => enter [1]; rw [← l75 sK1 sK2 sK0]
  have l82 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l52 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1]; rw [l81 sK0 sK1 sK2]
  have l83 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l82 sK0 sK1 sK2]
  have l84 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l83 sK0 sK1 sK2]
  have l85 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l52 (sK1 ◇ sK2) sK0]
  have l86 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l52 (sK1 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [l38 sK1 sK2]
  have l87 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l1 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l52 X0 sK0]
  have l88 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l52 X0 sK0]
  have l89 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l88 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l90 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l86 sK1 sK2 sK0]
    conv => enter [1]; rw [← l43 sK1 sK2]
  have l91 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l85 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l92 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l90 sK1 sK2 sK0]
    conv => enter [1]; rw [l52 (sK1 ◇ sK2) sK0]
  have l93 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l91 sK0 sK1 sK2]
    conv => enter [1]; rw [← l49 sK0 (sK1 ◇ sK2)]
  have l94 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l92 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l95 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l93 sK0 sK1 sK2]
    conv => enter [1]; rw [l89 sK0 sK0 (sK1 ◇ sK2)]
  have l96 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l94 sK1 sK2 sK0]
  have l97 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l95 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
  have l98 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l96 sK0 sK1 sK2]
  have l99 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l98 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK1 ◇ sK2) X0]
  have l100 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l98 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK2) X0]
  have l101 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l99 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X0 (sK1 ◇ sK2)]
  have l102 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41558 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2, 2, 2]; rw [← l37 sK1 sK2 sK0]
  have l103 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l102 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l19 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l104 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l103 X0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l56 sK1 sK2 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l105 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l104 X0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l78 sK1 sK2 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l106 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l105 X0 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← l87 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l107 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l106 X0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l19 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l108 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l107 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l109 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l108 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l1 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l110 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l109 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l87 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l111 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l110 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l89 sK0 sK0 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l112 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l111 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l113 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l112 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l100 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l114 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l113 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l52 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK0]
  have l115 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l114 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ sK0)]
  have l116 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l115 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l65 sK0 sK1 sK2]
  have l117 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l84 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l118 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l117 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l119 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l118 sK0 sK1 sK2]
    conv => enter [1]; rw [← l75 sK1 sK2 sK0]
  have l120 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l84 sK0 sK1 sK2]
    conv => enter [1]; rw [← l119 sK0 sK1 sK2]
  have l121 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l116 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l120 sK0 sK1 sK2]
  have l122 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l121 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l123 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l52 sK0 sK0]
    conv => enter [1]; rw [l122 sK0 sK1 sK2]
  have l124 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l101 sK0 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l91 sK0 sK1 sK2]
  have l125 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l124 sK0 sK1 sK2]
    conv => enter [1]; rw [l97 sK0 sK1 sK2]
  have l126 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l98 sK0 sK1 sK2]
    conv => enter [1]; rw [← l125 sK0 sK1 sK2]
  have l127 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l126 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ sK0)]
  have l128 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l123 sK0 sK1 sK2]
    conv => enter [1]; rw [← l127 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l128 x y z]

theorem Equation43_4512_41558_implies_Equation41543 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41558 : Equation41558 G) : Equation41543 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l2 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l5 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 sK0 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0 X0]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK2 ◇ (sK3 ◇ sK0))]
  have l10 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
  have l14 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h41558 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l16 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [h41558 (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1]; rw [← l4 sK1 sK2 sK3 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l17 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [h41558 (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l18 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [h41558 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← h41558 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) sK1]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← h41558 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK1]
  have l21 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l16 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← h41558 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) sK1]
  have l22 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1 sK1]
    conv => enter [1]; rw [← h41558 (sK1 ◇ sK1) sK1]
  have l23 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41558 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l24 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l19 sK1 sK2 sK3 sK0]
  have l25 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0]
  have l26 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l21 sK1 sK2 sK3 sK0]
  have l27 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l22 sK1]
  have l28 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
    conv => enter [1]; rw [l24 sK1 sK2 sK3 sK0]
  have l29 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l25 sK1 sK2 sK3 sK0]
  have l30 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
    conv => enter [1]; rw [l26 sK1 sK2 sK3 sK0]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l27 sK1]
  have l32 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l29 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK3 ◇ sK0))]
  have l33 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l26 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l28 sK1 sK2 sK3 sK0]
  have l34 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
    conv => enter [1]; rw [l33 sK1 sK2 sK3 sK0]
  have l35 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l34 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l32 sK2 sK3 sK0 sK1]
  have l36 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41558 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l31 sK1]
  have l37 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l36 X0 sK1]
    conv => enter [1, 2]; rw [l13 (sK1 ◇ sK1) (sK1 ◇ sK1) sK1 (sK1 ◇ sK1)]
  have l38 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l37 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l23 (sK1 ◇ sK1) sK1]
  have l39 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l38 X0 sK1]
    conv => enter [1, 2]; rw [← l23 sK1 sK1]
  have l40 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
    conv => enter [1, 2]; rw [l32 sK2 sK3 sK0 sK1]
  have l41 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) = (((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [l32 sK2 sK3 sK0 sK1]
  have l42 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [l41 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l43 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [← l40 sK1 sK2 sK3 sK0]
  have l44 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l43 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l35 sK1 sK2 sK3 sK0]
  have l45 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l39 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK1]
    conv => enter [1]; rw [l44 sK1 sK2 sK3 sK0]
  have l46 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l45 sK1 sK2 sK3 sK0]
  have l47 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l46 sK1 sK2 sK3 sK0]
  have l48 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l14 sK1 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l39 (sK2 ◇ (sK3 ◇ sK0)) sK1]
  have l49 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l1 X1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l39 X0 sK1]
  have l50 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 1]; rw [← l39 X0 sK1]
  have l51 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [l39 X0 sK1]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
  have l52 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l50 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l53 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l48 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK1)]
  have l54 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l53 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK2 sK3 sK0 (sK1 ◇ sK1)]
  have l55 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l54 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK1 ◇ sK1)]
  have l56 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l47 sK1 sK2 sK3 sK0]
  have l57 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [l47 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l58 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1]; rw [l57 sK1 sK2 sK3 sK0 X0]
  have l59 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l60 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l39 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK1]
    conv => enter [1]; rw [l59 sK1 sK2 sK3 sK0]
  have l61 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l60 sK1 sK2 sK3 sK0]
  have l62 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l61 sK1 sK2 sK3 sK0]
  have l63 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h41558 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
    conv => enter [1, 2, 2, 2]; rw [← l30 sK2 sK3 sK0 sK1]
  have l64 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l30 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
  have l65 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l64 X0 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l52 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) sK1 X0]
  have l66 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l63 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l13 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l67 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l65 X0 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l68 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l66 X0 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [l42 sK2 sK3 sK0 sK1 ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l69 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1, 2]; rw [← l32 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l67 X0 sK2 sK3 sK0 sK1]
  have l70 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l68 X0 sK2 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l58 sK1 sK2 sK3 sK0 ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l71 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l47 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l69 X0 sK2 sK3 sK0 sK1]
  have l72 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l70 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2, 2]; rw [← l49 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l73 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l72 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l52 sK1 sK1 ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l74 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l73 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l75 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l74 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l49 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l76 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l75 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l71 (sK1 ◇ sK1) sK1 sK2 sK3 sK0]
  have l77 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l76 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) (sK1 ◇ sK1)]
  have l78 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l77 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l3 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l79 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l78 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l52 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l80 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l79 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l81 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l80 X0 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l62 sK1 sK2 sK3 sK0]
  have l82 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [← l51 (sK2 ◇ (sK3 ◇ sK0)) sK1]
    conv => enter [1]; rw [l1 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK3 ◇ sK0))]
  have l83 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l47 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l82 sK1 sK2 sK3 sK0]
  have l84 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l52 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l83 sK1 sK2 sK3 sK0]
  have l85 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l84 sK1 sK2 sK3 sK0]
  have l86 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l85 sK1 sK2 sK3 sK0]
  have l87 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
    conv => enter [1, 2]; rw [l55 sK2 sK3 sK0 sK1]
  have l88 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l87 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l52 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
  have l89 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l81 sK1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l88 sK1 sK2 sK3 sK0]
  have l90 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l89 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l35 sK1 sK2 sK3 sK0]
  have l91 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l90 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l47 sK1 sK2 sK3 sK0]
  have l92 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l91 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l86 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l92 x y z w]

theorem Equation43_4512_41558_implies_Equation41559 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41558 : Equation41558 G) : Equation41559 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK2]
    conv => enter [1, 2]; rw [l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l6 sK1 sK2]
  have l9 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l10 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
  have l14 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l15 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l16 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK2) X0]
  have l17 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h41558 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41558 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41558 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l20 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l21 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l22 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h41558 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK0]
  have l25 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h41558 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
    conv => enter [1]; rw [← l22 sK1 sK2 sK1]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l21 sK1 sK2 sK1]
    conv => enter [1]; rw [← h41558 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK2 sK1]
    conv => enter [1]; rw [← h41558 (sK1 ◇ sK2) sK1]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0 sK0]
    conv => enter [1]; rw [← h41558 (sK0 ◇ sK0) sK0]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l30 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l17 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X1)) X2]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
  have l32 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2]
  have l34 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l27 sK1 sK2]
  have l35 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l28 sK0]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l37 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l30 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l38 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l39 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2))]
  have l40 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l33 sK1 sK2]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l35 sK0]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
    conv => enter [1]; rw [l14 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l43 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l37 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l44 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l40 sK1 sK2]
  have l45 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l43 X0 X2 X1]
  have l46 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l34 sK1 sK2]
  have l47 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l46 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l48 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l47 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l49 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41558 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2, 2, 2]; rw [← l38 sK1 sK2 sK0]
  have l50 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l38 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l51 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l49 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l13 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l52 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l51 X0 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← l50 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK1 sK2 sK0]
  have l53 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l52 X0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l13 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l54 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l53 X0 sK1 sK2 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l38 sK1 sK2 sK0]
  have l55 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l54 X0 X0 X0 sK0]
    conv => enter [1, 2]; rw [← l42 sK0 X0 X0]
  have l56 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l39 sK1 sK2]
  have l57 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l58 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l57 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ sK2))]
  have l59 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l44 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l60 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l59 sK1 sK2]
  have l61 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l60 sK1 sK2]
    conv => enter [1]; rw [l55 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l62 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l61 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l63 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [l55 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l64 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l63 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l65 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l64 sK1 sK2 sK0]
  have l66 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l65 sK1 sK2 sK0]
  have l67 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h41558 X0 X1]
    conv => enter [1]; rw [l55 X0 sK0]
  have l68 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l55 sK2 sK0]
  have l69 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [l55 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l70 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l55 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1]; rw [l39 sK1 sK2]
  have l71 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l55 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK0]
    conv => enter [1]; rw [← l38 sK1 sK2 sK0]
  have l72 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l55 X0 sK0]
  have l73 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l55 X0 sK0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
  have l74 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l72 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l75 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l71 sK0 sK1 sK2]
    conv => enter [1]; rw [l58 sK1 sK2 sK0]
  have l76 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l70 sK1 sK2 sK0]
    conv => enter [1]; rw [l62 sK1 sK2 sK0]
  have l77 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l69 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l78 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l68 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ sK0)]
  have l79 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
  have l80 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l76 sK1 sK2 sK0]
  have l81 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l78 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l82 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l80 sK0 sK1 sK2]
  have l83 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 (sK1 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l62 sK1 sK2 sK0]
  have l84 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l83 sK1 sK2 sK0]
    conv => enter [1]; rw [l74 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l85 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l84 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l86 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l82 sK0 sK1 sK2]
    conv => enter [1]; rw [← l85 sK1 sK2 sK0]
  have l87 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l48 sK1 sK2]
    conv => enter [1]; rw [l66 sK1 sK2 sK0]
  have l88 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l82 sK0 sK1 sK2]
    conv => enter [1]; rw [← l87 sK1 sK2 sK0]
  have l89 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l88 sK0 sK1 sK2]
    conv => enter [1]; rw [l55 (sK1 ◇ sK2) sK0]
  have l90 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l89 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l91 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41558 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l73 X0 sK0]
  have l92 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l73 sK2 sK0]
  have l93 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l73 (sK1 ◇ sK2) sK0]
  have l94 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l93 sK1 sK2 sK1]
    conv => enter [1]; rw [l74 sK1 sK1 (sK1 ◇ sK2)]
  have l95 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l74 sK1 sK1 sK2]
    conv => enter [1]; rw [← l92 sK2 sK1 sK1]
  have l96 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [← l94 sK1 sK2]
  have l97 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l95 sK1 sK2]
    conv => enter [1]; rw [h43 sK2 (sK1 ◇ sK2)]
  have l98 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l96 sK1 sK2]
    conv => enter [1]; rw [← l48 sK1 sK2]
  have l99 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l97 sK1 sK2]
    conv => enter [1]; rw [l34 sK1 sK2]
  have l100 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l98 sK1 sK2]
    conv => enter [1]; rw [l55 (sK1 ◇ sK2) sK0]
  have l101 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l99 sK1 sK2]
    conv => enter [1]; rw [l55 (sK1 ◇ sK2) sK0]
  have l102 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l100 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l103 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l101 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l104 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l102 sK1 sK2 sK0]
    conv => enter [1]; rw [← l90 sK0 sK1 sK2]
  have l105 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l103 sK1 sK2 sK0]
    conv => enter [1]; rw [← l90 sK0 sK1 sK2]
  have l106 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l104 sK1 sK2 sK0]
  have l107 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l105 sK1 sK2 sK0]
  have l108 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l107 sK1 sK2 sK0]
  have l109 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l108 sK1 sK2 sK1]
    conv => enter [1]; rw [← l106 sK1 sK2 sK1]
  have l110 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [l109 sK1 sK2]
  have l111 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l110 sK1 sK2 sK0]
  have l112 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l111 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l113 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l112 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l114 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [← l79 sK0 sK1 sK2]
  have l115 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l114 sK1 sK2 sK0]
    conv => enter [1]; rw [l74 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l116 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l115 sK1 sK2 sK0]
    conv => enter [1]; rw [← l113 sK0 sK1 sK2 sK1]
  have l117 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l116 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) sK1]
  have l118 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l111 sK0 sK1 sK2]
    conv => enter [1]; rw [← l117 sK1 sK2 sK0]
  have l119 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l118 sK0 sK1 sK2]
    conv => enter [1, 1]; rw [← l109 sK1 sK2]
  have l120 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l119 sK0 sK1 sK2]
    conv => enter [1]; rw [← l86 sK0 sK1 sK2]
  have l121 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l106 sK1 sK2 sK0]
    conv => enter [1]; rw [← l120 sK0 sK1 sK2]
  have l122 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l109 sK1 sK2]
    conv => enter [1]; rw [l121 sK1 sK2 sK0]
  have l123 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l77 sK1 sK2 sK0]
  have l124 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l123 sK1 sK2 sK0]
    conv => enter [1]; rw [l74 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l125 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l124 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l126 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l82 sK0 sK1 sK2]
    conv => enter [1]; rw [← l125 sK1 sK2 sK0]
  have l127 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l122 sK1 sK2 sK0]
    conv => enter [1]; rw [← l126 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l122 sK1 sK2 sK0]
  have l128 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l109 sK1 sK2]
    conv => enter [1]; rw [← l127 sK1 sK2 sK0]
  have l129 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l122 sK1 sK2 sK1]
    conv => enter [1]; rw [l128 sK1 sK1 sK2]
  have l130 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l129 sK1 sK2]
    conv => enter [1]; rw [← l48 sK1 sK2]
  have l131 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l129 sK1 sK2]
  have l132 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l109 sK1 sK2]
    conv => enter [1]; rw [← l131 sK0 sK1 sK2]
  have l133 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l130 sK1 sK2]
    conv => enter [1]; rw [l55 (sK1 ◇ sK2) sK0]
  have l134 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l122 sK1 sK2 sK1]
    conv => enter [1]; rw [l132 sK1 sK1 sK2]
    conv => enter [1, 1]; rw [← l122 sK1 sK2 sK1]
  have l135 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l133 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l136 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [l45 X0 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2, 2, 2]; rw [l81 sK1 sK2 sK0]
  have l137 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))))) = (X0 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1, 2, 2, 2, 2]; rw [l134 sK1 sK2]
    conv => enter [1]; rw [← l45 X0 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l138 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l67 X0 (X0 ◇ (X0 ◇ sK2)) sK0]
    conv => enter [1]; rw [l137 X0 X0 sK2]
  have l139 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l91 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l136 X0 sK2 sK1 X0]
  have l140 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l138 X0 sK0 sK2]
    conv => enter [1]; rw [← l139 X0 sK1 sK2]
  have l141 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l140 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l55 (sK1 ◇ sK2) sK0]
  have l142 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l141 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l143 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l142 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l90 sK0 sK1 sK2]
  have l144 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l143 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l106 sK1 sK2 sK0]
  have l145 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l144 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l109 sK1 sK2]
  have l146 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l135 sK1 sK2 sK0]
    conv => enter [1]; rw [l16 sK1 (sK0 ◇ sK0) sK2]
  have l147 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l146 sK1 sK2 sK0]
    conv => enter [1]; rw [← l145 (sK0 ◇ sK0) sK0 sK1 sK2]
  have l148 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l147 sK1 sK2 sK0]
    conv => enter [1]; rw [← l41 sK0]
  have l149 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l55 sK0 sK0]
    conv => enter [1]; rw [← l148 sK1 sK2 sK0]
  have l150 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l149 sK0 sK1 sK0]
    conv => enter [1]; rw [← l145 sK1 sK0 sK1 sK0]
  have l151 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l150 sK0 sK1]
    conv => enter [1]; rw [← l55 sK1 sK0]
  have l152 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l138 sK1 sK1 sK2]
    conv => enter [1]; rw [← l55 sK1 sK1]
  have l153 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l151 sK0 sK1]
    conv => enter [1]; rw [← l152 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l153 x y z]
  conv => enter [1]; rw [l122 y z x]

theorem Equation43_4512_41543_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41543 : Equation41543 G) : Equation308 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l4 X2 X0 X1]
  have l6 : ∀ X1 X0 X2 X3 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h41543 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [l4 X1 X0 (X2 ◇ X3)]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41543 sK0 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l8 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41543 (sK0 ◇ sK0) (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [l3 sK0 sK1 (X0 ◇ X1)]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, ((X0 ◇ X0) ◇ X4) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X4)) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1, 1]; rw [h41543 X0 X1 X2 X3]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l10 : ∀ X0 X4 X1 X2 X3 : G, ((X0 ◇ X0) ◇ X4) = (X0 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l9 X0 X4 X1 X2 X3]
    conv => enter [1]; rw [← l1 X0 X4 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l11 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) (sK0 ◇ sK0)]
  have l12 : ∀ X0 X4 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X4
    conv => enter [1]; rw [l6 X0 X4 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l10 X0 X4 X0 X0 X0]
  have l13 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l5 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) (sK0 ◇ sK0)]
  have l14 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [l12 X0 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK0 sK0 sK0 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l14 (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation43_4512_41543_implies_Equation41530 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41543 : Equation41543 G) : Equation41530 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41543 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41543 sK0 (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ X1)]
  have l8 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41543 X0 X1 X2 X3]
  have l9 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK0 ◇ sK1) X0 X1 X2]
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l10 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK0 ◇ sK1) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l11 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l10 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l13 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l8 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l14 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
  have l15 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ X1)]
  have l16 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l11 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [h43 (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ sK1))]
  have l17 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l12 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [h43 (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l18 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l13 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l19 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l16 sK0 sK1 X0 X1 X2]
  have l20 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l17 sK0 sK1 X0 X1 X2]
  have l21 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l18 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X3) X4]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l15 sK0 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l19 sK0 sK1 sK0 sK0 sK0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK0 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l20 sK0 sK1 sK0 sK0 sK0]
  have l24 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41543 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l21 X0 X4 X0 X0 X0]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1 X0]
    conv => enter [1]; rw [← l24 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l34 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1 X0]
  have l38 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1, 1]; rw [← l35 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l38 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l43 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [← l42 sK0 sK1 X0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l41 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y
  conv => enter [1]; rw [l44 x y]
  conv => enter [1]; rw [l35 x y]

theorem Equation43_4512_41543_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41543 : Equation41543 G) : Equation41532 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1)]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l12 sK0 sK1 X0]
  have l14 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l6 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l15 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l10 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK1 ◇ sK1)) X1]
  have l17 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = ((X0 ◇ sK1) ◇ (sK1 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1, 1]; rw [l6 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ sK1) X1]
  have l18 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ X1) = ((X0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (X0 ◇ (sK1 ◇ sK1)) X1]
  have l19 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l20 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l21 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X1 (X0 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = (sK1 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l17 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK1 X1 (X0 ◇ sK1)]
  have l23 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l16 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1]; rw [l20 sK1 sK0 X0]
  have l25 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l21 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l15 sK0 sK1 X1 X0]
  have l26 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = ((sK1 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l22 sK1 X0 X1]
    conv => enter [1]; rw [← l14 sK1 X1 X0]
  have l27 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l23 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l7 sK0 sK1 X1 X0]
  have l28 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 X1]
    conv => enter [1]; rw [l25 sK0 sK1 X0 X1]
  have l29 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l26 sK1 X0 X1]
  have l30 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l27 sK0 sK1 X0 X1]
  have l31 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41543 sK0 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X1)]
  have l32 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41543 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l33 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [h41543 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ X2))]
  have l34 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK1 ◇ sK1) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l35 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK0 ◇ (sK1 ◇ sK1)) X0 X1 X2]
    conv => enter [1]; rw [← l2 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l36 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK0 ◇ (sK1 ◇ sK1)) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l37 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l38 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l37 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l39 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l36 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l40 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l35 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l41 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l34 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK1 ◇ sK1))]
  have l42 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l32 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ X1)]
  have l43 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l31 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l44 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l38 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l28 sK0 sK1 (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l45 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l39 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l24 sK1 sK0 (X0 ◇ (X1 ◇ X2))]
  have l46 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l40 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l30 sK0 sK1 (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l47 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l41 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [l29 sK1 (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK1 ◇ sK1))]
  have l48 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l44 sK0 sK1 X0 X1 X2]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l45 sK0 sK1 sK1 sK1 sK1]
  have l50 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l46 sK0 sK1 X0 X1 X2]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l47 sK0 sK1 sK1 sK1 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l48 sK0 sK1 sK0 sK0 sK0]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l42 sK0 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l50 sK0 sK1 sK0 sK0 sK0]
  have l55 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1))]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK1 ◇ sK1))]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l55 sK1 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l58 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l62 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l63 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l64 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l43 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l63 X0 sK0 sK0]
  have l65 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l43 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l62 sK0 X0 sK0]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l57 sK1 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l57 sK1 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK1 ◇ sK1))]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l61 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 (sK1 ◇ sK1)]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK1 ◇ sK1)]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l66 sK1 sK0]
    conv => enter [1]; rw [← l71 sK0 sK1]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l72 sK1 sK0]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK0]
    conv => enter [1, 2]; rw [l73 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l74 x y]
  conv => enter [1]; rw [l69 x y]

end CommutativeSemigroup5
