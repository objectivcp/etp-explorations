import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_41543_implies_Equation41533 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41543 : Equation41543 G) : Equation41533 G := by
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
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK1 ◇ sK2))]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [l10 sK0 sK1 sK2 X0]
  have l12 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l13 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = ((X0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK1 ◇ sK2)) X1]
  have l14 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = ((X0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l8 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (X0 ◇ (sK1 ◇ sK2)) X1]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [← l9 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l16 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l17 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X1 (X0 ◇ (sK1 ◇ sK2))]
  have l18 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK1 ◇ sK2))]
  have l19 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1]; rw [l16 sK1 sK2 sK0 X0]
  have l20 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l17 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2 X1 X0]
  have l21 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X1 X0]
  have l22 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 X1]
    conv => enter [1]; rw [l20 sK0 sK1 sK2 X0 X1]
  have l23 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0 X1]
  have l24 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h41543 sK0 (sK1 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
  have l25 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h41543 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
  have l26 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41543 X0 X1 X2 X3]
  have l27 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = (X4 ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 2]; rw [← h41543 X0 X1 X2 X3]
  have l28 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK0 ◇ (sK1 ◇ sK2)) X0 X1 X2]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l29 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK0 ◇ (sK1 ◇ sK2)) X0 X1 X2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l30 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l31 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l30 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l32 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l29 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l33 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l34 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l27 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l35 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l26 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l36 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l25 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (X0 ◇ X1)]
  have l37 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l24 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
  have l38 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l31 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l22 sK0 sK1 sK2 (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l39 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l32 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [l23 sK0 sK1 sK2 (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l40 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l33 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ (X1 ◇ X2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l41 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l34 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X3) X4]
  have l42 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
    conv => enter [1]; rw [l35 X0 X1 X2 X3 X4]
  have l43 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l38 sK0 sK1 sK2 X0 X1 X2]
  have l44 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l39 sK0 sK1 sK2 X0 X1 X2]
  have l45 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l40 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← l19 sK1 sK2 sK0 (X0 ◇ (X1 ◇ X2))]
  have l46 : ∀ X0 X4 : G, (X0 ◇ X0) = (X4 ◇ (X0 ◇ X0)) := by
    intro X0 X4
    conv => enter [1]; rw [h41543 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l41 X4 X0 X0 X0 X0]
  have l47 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l42 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X3) X4]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l43 sK0 sK1 sK2 sK0 sK0 sK0]
  have l49 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l36 sK0 sK1 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l44 sK0 sK1 sK2 sK0 sK0 sK0]
  have l50 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l36 sK0 sK1 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l45 sK0 sK1 sK2 sK1 sK1 sK1]
  have l51 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41543 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l47 X0 X4 X0 X0 X0]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK1 ◇ sK2))]
  have l54 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l50 sK1 sK2 sK0]
    conv => enter [1]; rw [← l46 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l55 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
  have l56 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l54 sK1 sK2 sK0]
  have l57 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l56 sK0 sK1 sK2]
  have l59 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l58 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l60 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l58 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l61 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l60 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l51 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l62 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK1 ◇ sK2))]
  have l63 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l58 sK0 sK1 sK2]
    conv => enter [1]; rw [← l61 X0 sK0 sK1 sK2]
  have l64 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [← l62 sK0 sK1 sK2]
  have l65 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l64 sK0 sK1 sK2]
  have l66 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l65 sK0 sK1 sK2]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l66 sK0 sK1 sK2]
    conv => enter [1]; rw [← l63 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [l67 x y z]
  conv => enter [1]; rw [l65 x y z]

theorem Equation4512_41543_implies_Equation41539 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41543 : Equation41543 G) : Equation41539 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h41543 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l1 sK0 sK1 sK2 X0 X1]
  have l3 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l1 sK0 sK0 sK0 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [l2 sK0 sK0 sK0 sK0 sK0 X2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_41543_implies_Equation41558 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41543 : Equation41543 G) : Equation41558 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l2 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h41543 X0 X0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41543 X0 X0 X0 X0]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41543 sK1 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ X1)]
  have l6 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41543 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41543 (sK1 ◇ sK1) (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [← l1 sK1 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41543 X0 X1 X2 X3]
  have l9 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [h41543 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ X2))]
  have l10 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41543 (sK1 ◇ sK1) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l11 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l10 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l0 (sK1 ◇ sK1) (X0 ◇ (X1 ◇ X2)) (sK1 ◇ (sK1 ◇ sK1))]
  have l12 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l8 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l13 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l7 sK1 X0 X1]
  have l14 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l5 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l15 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l11 sK1 X0 X1 X2]
    conv => enter [1]; rw [← l3 sK1 (X0 ◇ (X1 ◇ X2))]
  have l16 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
    conv => enter [1]; rw [l12 X0 X1 X2 X3 X4]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 sK1]
    conv => enter [1]; rw [← l13 sK1 sK1 sK1]
  have l18 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l15 sK1 sK1 sK1 sK1]
  have l19 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l16 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X3) X4]
  have l20 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l14 sK1 X0 X1]
    conv => enter [1, 1]; rw [← l17 sK1]
  have l21 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l22 : ∀ X0 X4 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X4)) := by
    intro X0 X4
    conv => enter [1]; rw [h41543 X0 X0 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l19 X0 X4 X0 X0 X0]
  have l23 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l24 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l23 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l25 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l23 sK1]
    conv => enter [1]; rw [← l0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l26 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l25 X0 sK1]
  have l27 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l24 sK1 X0]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1, 2]; rw [l17 sK1]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l29 sK0]
  have l31 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l30 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l32 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l31 X0 sK0]
    conv => enter [1]; rw [← l22 (sK0 ◇ sK0) X0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [← l32 X0 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l27 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l34 x y]
  conv => enter [1]; rw [l28 y x]

theorem Equation43_4512_41539_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41539 : Equation41539 G) : Equation308 G := by
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
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK1)) X1]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l8 X2 X0 X1]
  have l10 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l11 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41539 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41539 X0 X1 X2]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41539 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ X1))]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) (sK0 ◇ sK0)]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) (sK0 ◇ sK0)]
  have l21 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l19 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l13 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l23 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l21 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l25 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41539 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l23 X0 X3 X0 X0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) (sK0 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l26 sK0 sK1 X0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l27 sK0 sK0 sK0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l28 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [← l25 (sK0 ◇ sK0) X0]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l30 sK0 X0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l32 x y]

theorem Equation4512_41539_implies_Equation41530 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41539 : Equation41539 G) : Equation41530 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h41539 X0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41539 X0 X0 X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41539 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l6 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41539 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l5 X0 X3 X0 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l8 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation43_4512_41539_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41539 : Equation41539 G) : Equation41532 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41539 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1 X0]
  have l9 : ∀ sK0 X1 sK1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1)) := by
    intro sK0 X1 sK1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) X1]
  have l10 : ∀ sK0 X1 sK1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l9 sK0 X1 sK1 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0 X1 sK0]
    conv => enter [1]; rw [← l10 sK0 X1 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation43_4512_41539_implies_Equation41533 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41539 : Equation41539 G) : Equation41533 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X1]
  have l4 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0 X1]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41539 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l8 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 sK2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X1 X0]
  have l9 : ∀ sK0 X1 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1)) := by
    intro sK0 X1 sK1 sK2 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) X1]
  have l10 : ∀ sK0 X1 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0))) := by
    intro sK0 X1 sK1 sK2 X0
    conv => enter [1]; rw [l9 sK0 X1 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0 sK0 X1 sK0]
    conv => enter [1]; rw [← l10 sK0 X1 sK0 sK0 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation43_4512_41539_implies_Equation41543 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41539 : Equation41539 G) : Equation41543 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) ◇ X1) = (sK1 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [l2 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X1]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X1))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X1]
  have l5 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X1))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 X0 X1]
  have l6 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h41539 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X1))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X1 X0]
  have l9 : ∀ sK1 X1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X1)) := by
    intro sK1 X1 sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [l7 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) X1]
  have l10 : ∀ sK1 X1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ X1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0))) := by
    intro sK1 X1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l9 sK1 X1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X1 ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)]
  have l11 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X1
    conv => enter [1]; rw [l8 sK1 sK1 sK1 sK1 X1 sK1]
    conv => enter [1]; rw [← l10 sK1 X1 sK1 sK1 sK1 sK1]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  intro x y z w
  conv => enter [1]; rw [l12 x y z w]

theorem Equation43_4512_41538_implies_Equation41529 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41538 : Equation41538 G) : Equation41529 G := by
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
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41538 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0) sK0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x
  conv => enter [1]; rw [l14 x]

theorem Equation43_4512_41538_implies_Equation4276 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41538 : Equation41538 G) : Equation4276 G := by
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
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l3 X2 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41538 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41538 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ X0))]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41538 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X0 ◇ X0))]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l7 sK0 sK0 (sK0 ◇ sK0) sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l18 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l19 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK1 ◇ sK1) sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 (sK0 ◇ sK0) (sK1 ◇ sK1)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [← l27 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l28 x y]

theorem Equation43_4512_41533_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41533 : Equation41533 G) : Equation308 G := by
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
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41533 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l1 X0 sK0 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41533 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK1 X0]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41533 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← l8 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation43_4512_41533_implies_Equation41530 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41533 : Equation41533 G) : Equation41530 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41533 (sK0 ◇ sK0) X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1 X0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41533 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41533 X0 X1 X2]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l4 sK0 sK1 X0]
  have l13 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l11 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) (sK0 ◇ sK0)]
  have l15 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l13 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)]
  have l17 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41533 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [← l15 X0 X3 X0 X0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0]
    conv => enter [1]; rw [← l16 sK0 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l18 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l17 (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation43_4512_41533_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41533 : Equation41533 G) : Equation41532 G := by
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
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l10 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l7 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l11 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l12 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = ((X0 ◇ sK1) ◇ (sK1 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1, 1]; rw [l7 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ sK1) X1]
  have l13 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = (sK1 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l12 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK1 X1 (X0 ◇ sK1)]
  have l14 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l15 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = ((sK1 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l13 sK1 X0 X1]
    conv => enter [1]; rw [← l10 sK1 X1 X0]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l15 sK1 X0 X1]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41533 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l1 X0 sK0 sK0]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41533 sK1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l1 X0 sK1 sK1]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41533 sK1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l7 sK1 X0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41533 (sK0 ◇ sK0) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK1 X0]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41533 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41533 X0 X1 X2]
  have l25 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X3 ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 2]; rw [← h41533 X0 X1 X2]
  have l26 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h41533 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))]
  have l27 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ (X0 ◇ X1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l26 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l28 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [← l25 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l29 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l24 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l5 sK0 sK1 X0]
  have l31 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l21 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l32 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l27 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l17 sK1 ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l28 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l36 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
    conv => enter [1]; rw [l29 X0 X1 X2 X3]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) (sK0 ◇ sK0)]
  have l38 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l34 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l18 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) (X0 ◇ X1)]
  have l39 : ∀ X0 X3 : G, (X0 ◇ X0) = (X3 ◇ (X0 ◇ X0)) := by
    intro X0 X3
    conv => enter [1]; rw [h41533 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [← l35 X3 X0 X0 X0]
  have l40 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l36 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l38 sK0 sK1 sK1 sK1]
  have l43 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41533 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [← l40 X0 X3 X0 X0]
  have l44 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0]
    conv => enter [1]; rw [← l41 sK0 sK0 sK0]
  have l45 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l42 sK1 sK1]
    conv => enter [1]; rw [← l39 (sK1 ◇ sK1) sK1]
  have l46 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l45 sK1]
    conv => enter [1]; rw [l0 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l47 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l45 sK1]
    conv => enter [1]; rw [l1 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l48 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l32 sK1 X0]
    conv => enter [1]; rw [← l47 X0 sK1]
  have l49 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l46 sK1 X0]
    conv => enter [1]; rw [← l43 (sK1 ◇ sK1) X0]
  have l50 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l48 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l49 sK1 X0]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l48 sK1 sK0]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l51 sK0 sK1]
  have l53 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l44 sK0]
    conv => enter [1]; rw [l1 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l54 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l53 X0 sK0]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l50 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l55 x y]
  conv => enter [1]; rw [l52 y x]

theorem Equation43_4512_41533_implies_Equation41539 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41533 : Equation41533 G) : Equation41539 G := by
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
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41533 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l1 X0 sK0 sK0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h41533 X0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41533 X0 X0 X0]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41533 X0 X1 X2]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41533 sK0 X0 X1]
    conv => enter [1]; rw [l1 sK0 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ X1)))]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) (sK0 ◇ sK0)]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (X0 ◇ X1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (X0 ◇ X1)) (sK0 ◇ sK0)]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (X0 ◇ X1))]
  have l18 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l16 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l19 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l17 sK0 X0 X1]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0) sK0 (X0 ◇ X1)]
  have l20 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41533 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [← l18 X0 X3 X0 X0]
  have l21 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1))]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0 sK0 sK0]
    conv => enter [1]; rw [← l20 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [l22 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l23 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l23 sK0]
    conv => enter [1]; rw [l1 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l25 X0 sK0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l20 (sK0 ◇ sK0) X0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l27 sK0 X0]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z
  conv => enter [1]; rw [l29 x y z]

theorem Equation43_4512_41532_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41532 : Equation41532 G) : Equation308 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK1) X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l11 sK0 (sK0 ◇ sK1) sK1]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41532 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ sK1)]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41532 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
  have l20 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l24 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1]; rw [← l22 sK0 sK0]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l20 sK0]
    conv => enter [1]; rw [l9 X0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l26 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l25 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l24 sK0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1, 2]; rw [← l1 X0 X0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [l9 sK0 X0 (X0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1, 2]; rw [← l26 X0 sK0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [← l1 X0 (sK0 ◇ sK0) X0]
  have l31 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l29 sK0 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ sK1)) sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l34 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l31 X1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l40 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l10 (sK0 ◇ sK1) X0 (sK0 ◇ sK1)]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l23 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l34 (sK0 ◇ (sK0 ◇ sK1)) sK0 (sK0 ◇ sK1)]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 (sK0 ◇ sK1) sK1]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l45 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l47 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l48 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l51 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l53 x y]

theorem Equation43_4512_41532_implies_Equation41530 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41532 : Equation41532 G) : Equation41530 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK1))]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l19 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l22 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l23 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l20 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1 (sK0 ◇ sK1)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [← l12 sK0 sK1 sK1]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l20 sK0 sK1 (sK0 ◇ sK1)]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ sK1)]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ sK1)]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1)]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l42 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l49 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1 X0]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l45 sK0 sK1]
  have l51 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0 sK0]
    conv => enter [1]; rw [l50 sK0 sK0]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l48 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0]
    conv => enter [1]; rw [← l52 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1))]
  have l55 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l51 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l58 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l57 sK0 sK0]
    conv => enter [1, 2]; rw [← l46 sK0 sK0]
  have l59 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l58 sK0]
    conv => enter [1]; rw [← l55 sK0 (sK0 ◇ sK0)]
  have l60 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l51 sK0]
    conv => enter [1]; rw [← l59 sK0]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l47 sK0 sK1]
  have l62 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l63 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l55 sK0 X0]
    conv => enter [1]; rw [← l62 sK0 sK1 X0]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41532 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2, 2]; rw [← l49 sK0 sK1 sK1]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1 ((sK0 ◇ sK0) ◇ sK1)]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l63 sK0 ((sK0 ◇ sK0) ◇ sK1) sK1]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l66 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l69 sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0]
    conv => enter [1]; rw [← l70 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l71 x y]

theorem Equation43_4512_41532_implies_Equation41533 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41532 : Equation41532 G) : Equation41533 G := by
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
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l10 sK0 sK1 sK2 X0]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l13 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK2]
  have l14 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l16 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = ((X0 ◇ sK2) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ sK2) X1]
  have l17 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (X1 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l16 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK1 X1 (X0 ◇ sK2)]
  have l18 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l19 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l17 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l13 sK1 sK2 X1 X0]
  have l20 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
  have l21 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l19 sK1 sK2 X0 X1]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
  have l23 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41532 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41532 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41532 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41532 (sK0 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l11 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41532 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l33 sK0 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l41 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [← l39 sK0 sK1 sK2]
  have l42 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0 sK0 sK0]
    conv => enter [1]; rw [l41 sK0 sK0 sK0]
  have l43 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X0]
  have l44 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 X0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l45 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l44 sK0 X0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l40 sK0 sK0 sK0]
  have l46 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l42 sK0]
  have l47 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1, 2]; rw [← l1 X0 X0 (sK0 ◇ sK0)]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l47 sK0 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (sK0 ◇ sK0)) sK0]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0]
    conv => enter [1, 2]; rw [h43 (X0 ◇ (sK0 ◇ sK0)) sK0]
  have l50 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1, 2]; rw [← l46 sK0 X0]
  have l51 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l50 sK0 X0]
    conv => enter [1]; rw [l1 X0 (sK0 ◇ sK0) X0]
  have l52 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l51 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l53 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l52 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l54 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41532 X0 sK0]
    conv => enter [1, 2]; rw [← l51 sK0 X0]
  have l55 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [h41532 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) X1]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h41532 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)))]
  have l57 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l56 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2))]
  have l58 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l55 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l59 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK2))]
  have l60 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l58 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l61 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l62 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l53 sK0 X1 X0]
    conv => enter [1]; rw [← l60 X0 X1 sK0]
  have l63 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l61 sK0 sK1 sK2]
    conv => enter [1]; rw [l23 (sK1 ◇ sK2) (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l64 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l62 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l65 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))]
  have l66 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l66 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l68 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l67 sK0 sK1 sK2]
    conv => enter [1]; rw [← l64 (sK1 ◇ sK2) sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l69 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l68 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l70 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l69 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l71 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← l70 sK0 sK1 sK2]
  have l72 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l71 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l73 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l72 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l74 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l73 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l75 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
    conv => enter [1]; rw [l54 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l76 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l77 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l76 sK0 sK1 sK2]
  have l78 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l54 sK0 sK0]
    conv => enter [1]; rw [← l77 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l78 x y z]

theorem Equation43_4512_41530_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41530 : Equation41530 G) : Equation308 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK1))]
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
  have l8 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l11 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41530 sK0 X0]
    conv => enter [1, 2, 2]; rw [l1 sK0 sK0 X0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41530 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [l11 sK0 (sK0 ◇ sK0) sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41530 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41530 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 2]; rw [l8 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l20 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l21 sK0]
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l22 sK0 X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l24 x y]

theorem Equation43_4512_41530_implies_Equation41532 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41530 : Equation41530 G) : Equation41532 G := by
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
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
  have l8 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41530 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41530 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ sK0)]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l19 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l20 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l19 sK0 X0 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0 sK0]
    conv => enter [1]; rw [← l20 sK0 X0 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation41529_53807_implies_Equation307 (G : Type*) [Magma G] (h41529 : Equation41529 G) (h53807 : Equation53807 G) : Equation307 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h41529 X0]
    conv => enter [1, 2]; rw [← h53807 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h53807 X0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation43_4512_41529_53807_implies_Equation53860 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) (h53807 : Equation53807 G) : Equation53860 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h41529 X0]
    conv => enter [1, 2]; rw [← h53807 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h53807 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation5571_implies_Equation2 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation2 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5571_implies_Equation4696 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4696 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5571_implies_Equation4698 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4698 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5571_implies_Equation4699 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4699 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5571_implies_Equation4704 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4704 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5571_implies_Equation4705 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4705 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5571_implies_Equation4709 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4709 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5571_implies_Equation4724 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4724 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5571_implies_Equation4725 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4725 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5571_implies_Equation4728 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4728 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5571_implies_Equation4729 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4729 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5571_implies_Equation4746 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4746 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5571_implies_Equation4799 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4799 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5571_implies_Equation4802 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4802 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5571_implies_Equation4803 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4803 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5571_implies_Equation4815 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4815 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5571_implies_Equation4820 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4820 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5571_implies_Equation4897 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4897 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5571_implies_Equation5100 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5100 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5571_implies_Equation5101 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5101 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5571_implies_Equation5104 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5104 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5571_implies_Equation5105 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5105 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5571_implies_Equation5116 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5116 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5571_implies_Equation5117 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5117 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5571_implies_Equation5122 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5122 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5571_implies_Equation5172 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5172 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5571_implies_Equation5173 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5173 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5571_implies_Equation5199 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation5199 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5571_implies_Equation4798 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4798 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5571_implies_Equation41805 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation41805 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1, 2]; rw [l0 y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation5571_implies_Equation4695 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation4695 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))]

@[equational_result]
theorem Equation5199_implies_Equation2 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5199_implies_Equation4696 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4696 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5199_implies_Equation4698 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4698 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5199_implies_Equation4699 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4699 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5199_implies_Equation4704 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4704 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5199_implies_Equation4705 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4705 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5199_implies_Equation4709 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4709 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5199_implies_Equation4724 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4724 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5199_implies_Equation4725 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4725 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5199_implies_Equation4728 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4728 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5199_implies_Equation4729 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4729 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5199_implies_Equation4746 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4746 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5199_implies_Equation4799 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4799 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5199_implies_Equation4802 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4802 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5199_implies_Equation4803 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4803 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5199_implies_Equation4815 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4815 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5199_implies_Equation4820 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4820 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5199_implies_Equation4897 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation4897 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5199_implies_Equation5100 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5100 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5199_implies_Equation5101 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5101 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5199_implies_Equation5104 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5104 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5199_implies_Equation5105 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5105 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5199_implies_Equation5116 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5116 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5199_implies_Equation5117 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5117 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5199_implies_Equation5122 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5122 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5199_implies_Equation5172 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5172 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5199_implies_Equation5173 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5173 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5199_implies_Equation5571 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation5571 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y z w u v r
  conv => enter [1]; rw [l0 x (y ◇ (z ◇ (w ◇ (u ◇ (v ◇ r)))))]

@[equational_result]
theorem Equation5173_implies_Equation2 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5173_implies_Equation4696 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4696 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5173_implies_Equation4698 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4698 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5173_implies_Equation4699 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4699 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5173_implies_Equation4704 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4704 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5173_implies_Equation4705 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4705 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5173_implies_Equation4709 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4709 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5173_implies_Equation4724 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4724 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5173_implies_Equation4725 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4725 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5173_implies_Equation4728 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4728 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5173_implies_Equation4729 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4729 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5173_implies_Equation4746 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4746 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5173_implies_Equation4799 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4799 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5173_implies_Equation4802 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4802 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5173_implies_Equation4803 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4803 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5173_implies_Equation4815 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4815 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5173_implies_Equation4820 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4820 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5173_implies_Equation4897 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation4897 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5173_implies_Equation5100 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation5100 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5173_implies_Equation5101 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation5101 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5173_implies_Equation5104 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation5104 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5173_implies_Equation5105 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation5105 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5173_implies_Equation5116 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation5116 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5173_implies_Equation5117 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation5117 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5173_implies_Equation5122 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation5122 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5173_implies_Equation5172 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation5172 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5173_implies_Equation5199 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation5199 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5172_implies_Equation2 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5172_implies_Equation4696 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4696 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5172_implies_Equation4698 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4698 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5172_implies_Equation4699 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4699 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5172_implies_Equation4704 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4704 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5172_implies_Equation4705 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4705 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5172_implies_Equation4709 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4709 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5172_implies_Equation4724 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4724 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5172_implies_Equation4725 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4725 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5172_implies_Equation4728 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4728 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5172_implies_Equation4729 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4729 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5172_implies_Equation4746 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4746 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5172_implies_Equation4799 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4799 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5172_implies_Equation4802 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4802 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5172_implies_Equation4803 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4803 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5172_implies_Equation4815 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4815 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5172_implies_Equation4820 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4820 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5172_implies_Equation4897 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation4897 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5172_implies_Equation5100 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation5100 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5172_implies_Equation5101 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation5101 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5172_implies_Equation5104 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation5104 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5172_implies_Equation5105 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation5105 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5172_implies_Equation5116 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation5116 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5172_implies_Equation5117 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation5117 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5172_implies_Equation5122 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation5122 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5172_implies_Equation5173 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation5173 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5122_implies_Equation2 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5122_implies_Equation4696 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4696 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5122_implies_Equation4698 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4698 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5122_implies_Equation4699 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4699 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5122_implies_Equation4704 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4704 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5122_implies_Equation4705 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4705 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5122_implies_Equation4709 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4709 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5122_implies_Equation4724 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4724 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5122_implies_Equation4725 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4725 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5122_implies_Equation4728 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4728 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5122_implies_Equation4729 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4729 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5122_implies_Equation4746 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4746 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5122_implies_Equation4799 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4799 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5122_implies_Equation4802 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4802 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5122_implies_Equation4803 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4803 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5122_implies_Equation4815 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4815 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5122_implies_Equation4820 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4820 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5122_implies_Equation4897 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation4897 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5122_implies_Equation5100 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation5100 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5122_implies_Equation5101 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation5101 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5122_implies_Equation5104 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation5104 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5122_implies_Equation5105 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation5105 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5122_implies_Equation5116 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation5116 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5122_implies_Equation5117 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation5117 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5122_implies_Equation5172 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation5172 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5117_implies_Equation2 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5117_implies_Equation4696 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4696 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5117_implies_Equation4698 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4698 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5117_implies_Equation4699 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4699 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5117_implies_Equation4704 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4704 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5117_implies_Equation4705 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4705 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5117_implies_Equation4709 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4709 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5117_implies_Equation4724 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4724 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5117_implies_Equation4725 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4725 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5117_implies_Equation4728 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4728 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5117_implies_Equation4729 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4729 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5117_implies_Equation4746 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4746 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5117_implies_Equation4799 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4799 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5117_implies_Equation4802 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4802 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5117_implies_Equation4803 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4803 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5117_implies_Equation4815 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4815 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5117_implies_Equation4820 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4820 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5117_implies_Equation4897 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation4897 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5117_implies_Equation5100 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation5100 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5117_implies_Equation5101 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation5101 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5117_implies_Equation5104 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation5104 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5117_implies_Equation5105 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation5105 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5117_implies_Equation5116 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation5116 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5117_implies_Equation5122 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation5122 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5116_implies_Equation2 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5116_implies_Equation4696 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4696 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5116_implies_Equation4698 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4698 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5116_implies_Equation4699 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4699 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5116_implies_Equation4704 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4704 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5116_implies_Equation4705 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4705 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5116_implies_Equation4709 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4709 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5116_implies_Equation4724 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4724 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5116_implies_Equation4725 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4725 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5116_implies_Equation4728 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4728 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5116_implies_Equation4729 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4729 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5116_implies_Equation4746 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4746 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5116_implies_Equation4799 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4799 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5116_implies_Equation4802 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4802 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5116_implies_Equation4803 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4803 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5116_implies_Equation4815 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4815 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5116_implies_Equation4820 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4820 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5116_implies_Equation4897 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation4897 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5116_implies_Equation5100 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation5100 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5116_implies_Equation5101 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation5101 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5116_implies_Equation5104 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation5104 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5116_implies_Equation5105 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation5105 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5116_implies_Equation5117 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation5117 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5105_implies_Equation2 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5105_implies_Equation4696 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4696 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5105_implies_Equation4698 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4698 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5105_implies_Equation4699 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4699 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5105_implies_Equation4704 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4704 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5105_implies_Equation4705 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4705 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5105_implies_Equation4709 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4709 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5105_implies_Equation4724 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4724 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5105_implies_Equation4725 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4725 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5105_implies_Equation4728 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4728 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5105_implies_Equation4729 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4729 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5105_implies_Equation4746 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4746 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5105_implies_Equation4799 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4799 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5105_implies_Equation4802 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4802 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5105_implies_Equation4803 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4803 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5105_implies_Equation4815 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4815 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5105_implies_Equation4820 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4820 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5105_implies_Equation4897 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation4897 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5105_implies_Equation5100 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation5100 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5105_implies_Equation5101 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation5101 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5105_implies_Equation5104 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation5104 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5105_implies_Equation5116 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation5116 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5104_implies_Equation2 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5104_implies_Equation4696 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4696 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5104_implies_Equation4698 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4698 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5104_implies_Equation4699 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4699 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5104_implies_Equation4704 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4704 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5104_implies_Equation4705 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4705 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5104_implies_Equation4709 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4709 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5104_implies_Equation4724 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4724 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5104_implies_Equation4725 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4725 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5104_implies_Equation4728 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4728 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5104_implies_Equation4729 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4729 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5104_implies_Equation4746 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4746 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5104_implies_Equation4799 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4799 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5104_implies_Equation4802 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4802 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5104_implies_Equation4803 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4803 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5104_implies_Equation4815 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4815 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5104_implies_Equation4820 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4820 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5104_implies_Equation4897 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation4897 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5104_implies_Equation5100 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation5100 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5104_implies_Equation5101 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation5101 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5104_implies_Equation5105 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation5105 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5101_implies_Equation2 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5101_implies_Equation4696 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4696 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5101_implies_Equation4698 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4698 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5101_implies_Equation4699 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4699 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5101_implies_Equation4704 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4704 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5101_implies_Equation4705 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4705 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5101_implies_Equation4709 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4709 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5101_implies_Equation4724 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4724 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5101_implies_Equation4725 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4725 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5101_implies_Equation4728 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4728 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

end CommutativeSemigroup5
