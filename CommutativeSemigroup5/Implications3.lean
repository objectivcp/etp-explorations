import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_41761_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41761 : Equation41761 G) : Equation42237 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l2 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l4 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) (sK2 ◇ sK2)]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l5 sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
  have l8 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [← l5 sK1 sK2]
    conv => enter [1]; rw [l0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l9 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l8 sK2 sK1 X0]
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK2 ◇ sK2)) X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l10 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0]
    conv => enter [1]; rw [l9 sK2 sK1 X0]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← l1 X2 X3 (X0 ◇ X1)]
  have l12 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 (X2 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 X2 X0]
  have l13 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h41761 X2 (X0 ◇ (X3 ◇ (X3 ◇ X1))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41761 X0 X1 X3]
  have l14 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l15 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h41761 X1 (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK1 sK2 X0]
  have l16 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41761 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l5 sK1 sK2]
  have l17 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41761 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2, 2, 2]; rw [l7 sK1 sK2]
  have l18 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41761 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l1 X1 X1 X0]
  have l19 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h41761 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK2 X0]
  have l20 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1, 2]; rw [l1 X2 X0 (X0 ◇ X1)]
  have l21 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = ((X0 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41761 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X2 ◇ (X2 ◇ X1))) X3]
  have l22 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41761 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2)))]
  have l23 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l22 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ X2))]
  have l24 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l21 X0 X1 X3 X2]
    conv => enter [1]; rw [← l1 X0 X3 (X0 ◇ (X2 ◇ (X2 ◇ X1)))]
  have l25 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l20 X2 X1 X0]
    conv => enter [1]; rw [l11 X2 (X0 ◇ X1) X2 X0]
  have l26 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l17 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l1 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l27 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l16 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l1 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) (sK1 ◇ (sK2 ◇ sK2))]
  have l28 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l15 X1 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l29 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l14 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 (X1 ◇ X2) (X0 ◇ X1)]
  have l30 : ∀ X2 X1 X0 X3 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1]; rw [← l13 X2 X0 X3 X1]
  have l31 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l23 X0 X1 X2 X3]
  have l32 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l24 X0 X1 X3 X2]
  have l33 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l26 X0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l10 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
  have l34 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l27 X0 sK1 sK2]
    conv => enter [1]; rw [← l19 X0 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2]
  have l35 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l29 X3 X2 X3 X1]
    conv => enter [1]; rw [← l12 X3 X1 (X1 ◇ X2) X3]
  have l36 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l31 X0 X1 X2 X3]
    conv => enter [1]; rw [← l25 X0 (X3 ◇ (X3 ◇ X2)) X1]
  have l37 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X3 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l32 X0 X1 X3 X0]
    conv => enter [1, 2]; rw [← l30 X3 X1 X0 X0]
  have l38 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l18 X0 (sK2 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
    conv => enter [1]; rw [← l33 X0 sK1 sK2]
  have l39 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l34 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) (sK1 ◇ (sK2 ◇ sK2))]
  have l40 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l35 X0 X2 X0]
    conv => enter [1]; rw [← l36 X0 X1 X2 X0]
  have l41 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l38 X0 sK2 sK1]
    conv => enter [1]; rw [l39 X0 sK1 sK2]
  have l42 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l41 X0 sK2 sK1]
    conv => enter [1]; rw [← l40 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) (sK1 ◇ (sK2 ◇ sK2))]
  have l43 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0]
    conv => enter [1]; rw [← l42 X0 sK2 sK1]
  have l44 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X1)) := by
    intro X1 X0 sK2 sK1
    conv => enter [1, 2]; rw [l42 X0 sK2 sK1]
    conv => enter [1]; rw [← l1 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X1]
  have l45 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l40 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ sK2))))]
    conv => enter [1]; rw [← l44 X1 X0 sK2 X0]
  have l46 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l45 X0 X1 sK2]
    conv => enter [1]; rw [← l40 X1 (sK2 ◇ sK2) X0]
  have l47 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (sK2 ◇ sK2))))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h41761 X1 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
    conv => enter [1, 2, 2, 2]; rw [l43 sK1 sK2 X0]
  have l48 : ∀ X1 X0 sK2 sK1 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK2 sK1
    conv => enter [1]; rw [l47 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← l28 X1 (X0 ◇ (sK2 ◇ sK2)) sK1 sK2]
  have l49 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2)))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l48 X1 X0 sK2 sK1]
    conv => enter [1]; rw [l37 X1 (X0 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
  have l50 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l49 X1 X0 X1 sK2]
    conv => enter [1]; rw [← l40 X1 (X0 ◇ (sK2 ◇ sK2)) (X1 ◇ (sK2 ◇ sK2))]
  have l51 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [l50 X1 X0 sK2]
    conv => enter [1]; rw [← l40 X1 (sK2 ◇ sK2) X0]
  have l52 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l46 (X0 ◇ X1) sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 sK1]
  have l53 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l52 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [l51 X0 (sK1 ◇ sK1) sK2]
  have l54 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l46 X0 X1 sK2]
    conv => enter [1]; rw [l53 X1 sK2 sK1]
  have l55 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l54 sK0 sK3 sK1 sK2]
    conv => enter [1]; rw [h43 sK0 sK3]
  have l56 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l54 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [l55 sK2 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l56 w x y]
  conv => enter [1]; rw [l54 w w z w]
  conv => enter [1]; rw [l38 z w z]

theorem Equation43_4512_41761_implies_Equation41737 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41761 : Equation41761 G) : Equation41737 G := by
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
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK1 ◇ sK2)]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l17 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK2]
  have l18 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = ((X0 ◇ sK2) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ sK2) X1]
  have l19 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [← l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l20 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l21 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (X1 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l18 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK1 X1 (X0 ◇ sK2)]
  have l22 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1]; rw [l20 sK1 sK2 sK0 X0]
  have l23 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l21 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l17 sK1 sK2 X1 X0]
  have l24 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l23 sK1 sK2 X0 X1]
  have l25 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← l1 X2 X3 (X0 ◇ X1)]
  have l26 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 (X2 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 X2 X0]
  have l27 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h41761 X2 (X0 ◇ (X3 ◇ (X3 ◇ X1))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41761 X0 X1 X3]
  have l28 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l29 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41761 X0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l10 sK0 sK1 sK2]
  have l30 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41761 X0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l14 sK0 sK1 sK2]
  have l31 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h41761 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2, 2]; rw [l16 sK0 sK1 sK2]
  have l32 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41761 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l1 X1 X1 X0]
  have l33 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1, 2]; rw [l1 X2 X0 (X0 ◇ X1)]
  have l34 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h41761 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ X0)]
  have l35 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = ((X0 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41761 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X2 ◇ (X2 ◇ X1))) X3]
  have l36 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41761 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2)))]
  have l37 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l36 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ X2))]
  have l38 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l35 X0 X1 X3 X2]
    conv => enter [1]; rw [← l1 X0 X3 (X0 ◇ (X2 ◇ (X2 ◇ X1)))]
  have l39 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) ((sK1 ◇ sK2) ◇ X0)]
  have l40 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l33 X2 X1 X0]
    conv => enter [1]; rw [l25 X2 (X0 ◇ X1) X2 X0]
  have l41 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l31 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l42 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l30 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l1 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
  have l43 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l29 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ sK1)]
  have l44 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l28 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 (X1 ◇ X2) (X0 ◇ X1)]
  have l45 : ∀ X2 X1 X0 X3 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1]; rw [← l27 X2 X0 X3 X1]
  have l46 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l37 X0 X1 X2 X3]
  have l47 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l38 X0 X1 X3 X2]
  have l48 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK2) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l49 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l41 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l22 sK1 sK2 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l50 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l42 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l24 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2))]
  have l51 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l43 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ sK1)]
  have l52 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l44 X3 X2 X3 X1]
    conv => enter [1]; rw [← l26 X3 X1 (X1 ◇ X2) X3]
  have l53 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l46 X0 X1 X2 X3]
    conv => enter [1]; rw [← l40 X0 (X3 ◇ (X3 ◇ X2)) X1]
  have l54 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X3 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l47 X0 X1 X3 X0]
    conv => enter [1, 2]; rw [← l45 X3 X1 X0 X0]
  have l55 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l32 X0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [← l49 X0 sK0 sK1 sK2]
  have l56 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l50 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l48 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l57 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l51 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2, 2]; rw [l9 sK0 sK1 sK2]
  have l58 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l52 X0 X2 X0]
    conv => enter [1]; rw [← l53 X0 X1 X2 X0]
  have l59 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l57 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h41761 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK1]
  have l60 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h41761 X0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l56 X0 sK0 sK1 sK2]
  have l61 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l59 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l62 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l59 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l63 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l59 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l64 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l58 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l63 sK0 sK1 sK2]
  have l65 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l62 sK1 sK2 sK0]
    conv => enter [1]; rw [l54 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l66 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l61 sK0 sK1 sK2]
    conv => enter [1]; rw [l54 (sK0 ◇ sK1) sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l64 sK0 sK1 sK2]
    conv => enter [1]; rw [← l59 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
  have l68 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l58 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l65 sK1 sK2 sK0]
  have l69 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l58 (sK0 ◇ sK1) sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l66 sK0 sK1 sK2]
  have l70 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l67 sK0 sK1 sK2]
    conv => enter [1]; rw [← l60 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2 sK0]
  have l71 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l68 sK1 sK2 sK0]
    conv => enter [1]; rw [← l59 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l72 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l69 sK0 sK1 sK2]
    conv => enter [1]; rw [← l59 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
  have l73 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l70 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l74 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l71 sK1 sK2 sK1]
    conv => enter [1]; rw [← l60 (sK1 ◇ sK2) sK1 sK2 sK1]
  have l75 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l72 sK0 sK1 sK2]
    conv => enter [1]; rw [← l60 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK2 sK0]
  have l76 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l73 sK0 sK1 sK2]
    conv => enter [1]; rw [← l60 (sK1 ◇ sK2) sK1 sK2 sK0]
  have l77 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l78 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l76 sK0 sK1 sK2]
  have l79 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l77 sK0 sK1 sK2]
    conv => enter [1]; rw [← l60 (sK1 ◇ sK2) sK1 sK2 sK0]
  have l80 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l74 sK1 sK2]
    conv => enter [1]; rw [← l78 sK0 sK1 sK2]
  have l81 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l74 sK1 sK2]
    conv => enter [1]; rw [← l79 sK0 sK1 sK2]
  have l82 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l80 sK1 sK2 sK0]
  have l83 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ X0) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l82 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l58 sK0 X0 (sK1 ◇ sK2)]
  have l84 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← l80 sK1 sK2 sK0]
  have l85 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l80 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l86 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l85 sK0 sK1 sK2]
    conv => enter [1]; rw [← l55 sK1 sK1 sK2 sK0]
  have l87 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l58 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l84 sK0 sK1 sK2 X0]
  have l88 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l80 sK1 sK2 sK0]
    conv => enter [1]; rw [l83 sK0 sK1 sK2 sK0]
  have l89 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l83 sK1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l86 sK0 sK1 sK2]
  have l90 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l87 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l83 sK0 sK1 sK2 sK0]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l89 sK0 sK1 sK0]
    conv => enter [1]; rw [l83 (sK0 ◇ sK1) sK1 sK0 sK0]
  have l92 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l88 sK0 sK1 sK2]
    conv => enter [1]; rw [← l90 sK0 sK1 sK2 X0]
  have l93 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l81 sK1 sK2 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) sK2 X0]
  have l94 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l93 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) X0 sK2]
  have l95 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l94 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l58 (sK0 ◇ sK1) sK2 X0]
  have l96 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← l95 sK1 sK2 X0 sK0]
  have l97 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l80 sK1 sK2 sK1]
    conv => enter [1]; rw [l96 sK1 sK1 sK2 X0]
  have l98 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l97 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) X0 X1]
  have l99 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l97 sK1 sK2 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ sK2)]
  have l100 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l99 sK0 sK1 sK2]
    conv => enter [1]; rw [l83 (sK0 ◇ sK1) sK1 sK2 sK0]
  have l101 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (sK1 ◇ sK2) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l58 X1 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l98 sK1 sK2 X1 X0]
  have l102 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [← l100 sK0 sK1 sK2]
  have l103 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l102 sK0 sK1 sK2]
    conv => enter [1]; rw [l101 sK0 (sK1 ◇ sK2) sK1 sK2]
  have l104 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l92 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 X1]
  have l105 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l101 sK1 sK2 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1)]
    conv => enter [1]; rw [← l104 sK0 sK1 sK2 sK1 sK1]
  have l106 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l103 sK0 sK1 sK2]
    conv => enter [1]; rw [l105 sK1 sK2 sK0]
  have l107 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l101 sK1 sK2 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l106 sK0 sK1 sK2]
  have l108 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l103 sK0 sK1 sK2]
    conv => enter [1]; rw [l107 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l108 x y z]

theorem Equation43_4512_41761_implies_Equation41741 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41761 : Equation41761 G) : Equation41741 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l3 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l4 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l5 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l2 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ sK3))]
  have l6 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l5 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK2 ◇ sK3)]
  have l7 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (X1 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l4 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK3]
  have l8 : ∀ sK2 sK3 X0 X1 : G, (((sK2 ◇ sK3) ◇ X0) ◇ X1) = ((X0 ◇ sK3) ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1, 1]; rw [l4 sK2 sK3 X0]
    conv => enter [1]; rw [l0 sK2 (X0 ◇ sK3) X1]
  have l9 : ∀ sK2 sK3 X0 X1 : G, (((sK2 ◇ sK3) ◇ X0) ◇ X1) = (sK2 ◇ (X1 ◇ (X0 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l8 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← l1 sK2 X1 (X0 ◇ sK3)]
  have l10 : ∀ sK2 sK3 X0 X1 : G, (((sK2 ◇ sK3) ◇ X0) ◇ X1) = ((sK2 ◇ sK3) ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l9 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← l7 sK2 sK3 X1 X0]
  have l11 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK3) ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) X0 X1]
    conv => enter [1]; rw [l10 sK2 sK3 X0 X1]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← l1 X2 X3 (X0 ◇ X1)]
  have l13 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 (X2 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 X2 X0]
  have l14 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l15 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h41761 X0 (sK1 ◇ (sK2 ◇ sK3)) (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2, 2, 2]; rw [l6 sK1 sK2 sK3]
  have l16 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1, 2]; rw [l1 X2 X0 (X0 ◇ X1)]
  have l17 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1]; rw [h41761 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK3) ((sK2 ◇ sK3) ◇ X0)]
  have l18 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41761 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2)))]
  have l19 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ X2))]
  have l20 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1]; rw [l17 sK1 X0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) ((sK2 ◇ sK3) ◇ X0)]
  have l21 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l16 X2 X1 X0]
    conv => enter [1]; rw [l12 X2 (X0 ◇ X1) X2 X0]
  have l22 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3)))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l15 X0 sK1 sK2 sK3]
    conv => enter [1, 2, 2]; rw [← l1 (sK2 ◇ sK3) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK2 ◇ sK3))]
  have l23 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l14 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 (X1 ◇ X2) (X0 ◇ X1)]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l19 X0 X1 X2 X3]
  have l25 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1]; rw [l20 sK1 X0 sK2 sK3]
    conv => enter [1]; rw [← l1 (sK2 ◇ sK3) X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l26 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l22 X0 sK1 sK2 sK3]
    conv => enter [1, 2, 2]; rw [l11 sK2 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK2 ◇ sK3))]
  have l27 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l23 X3 X2 X3 X1]
    conv => enter [1]; rw [← l13 X3 X1 (X1 ◇ X2) X3]
  have l28 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l24 X0 X1 X2 X3]
    conv => enter [1]; rw [← l21 X0 (X3 ◇ (X3 ◇ X2)) X1]
  have l29 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l26 X0 sK1 sK2 sK3]
    conv => enter [1, 2, 2]; rw [← l25 sK1 (sK1 ◇ (sK2 ◇ sK3)) sK2 sK3]
  have l30 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l27 X0 X2 X0]
    conv => enter [1]; rw [← l28 X0 X1 X2 X0]
  have l31 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [h41761 X0 (sK2 ◇ sK3) sK1]
    conv => enter [1]; rw [← l29 X0 sK1 sK2 sK3]
  have l32 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 X0]
    conv => enter [1, 2, 2]; rw [← l31 sK1 sK2 sK3 sK1]
  have l33 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l30 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [← l32 sK1 sK2 sK3 X0]
  have l34 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l31 sK1 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l31 sK1 sK2 sK3 sK1]
  have l35 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l31 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l33 sK1 sK2 sK3 X0]
  have l36 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l35 sK1 sK2 sK3 X0]
    conv => enter [1, 1]; rw [← l34 sK1 sK2 sK3]
  have l37 : ∀ sK1 sK2 sK3 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1]; rw [l36 sK1 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK2 ◇ sK3)) X0 X1]
  have l38 : ∀ X1 X0 sK1 sK2 sK3 : G, (X1 ◇ X0) = (sK1 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 sK1 sK2 sK3
    conv => enter [1]; rw [l30 X1 X0 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l37 sK1 sK2 sK3 X1 X0]
  intro x y z w
  conv => enter [1]; rw [l38 x y x z w]
  conv => enter [1]; rw [l34 x z w]

theorem Equation43_4512_41761_implies_Equation42225 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41761 : Equation41761 G) : Equation42225 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l3 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l4 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l5 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l2 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ sK3))]
  have l6 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l5 sK1 sK2 sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK2 ◇ sK3)]
  have l7 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (X1 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l4 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK3]
  have l8 : ∀ sK2 sK3 X0 X1 : G, (((sK2 ◇ sK3) ◇ X0) ◇ X1) = ((X0 ◇ sK3) ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1, 1]; rw [l4 sK2 sK3 X0]
    conv => enter [1]; rw [l0 sK2 (X0 ◇ sK3) X1]
  have l9 : ∀ sK2 sK3 X0 X1 : G, (((sK2 ◇ sK3) ◇ X0) ◇ X1) = (sK2 ◇ (X1 ◇ (X0 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l8 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← l1 sK2 X1 (X0 ◇ sK3)]
  have l10 : ∀ sK2 sK3 X0 X1 : G, (((sK2 ◇ sK3) ◇ X0) ◇ X1) = ((sK2 ◇ sK3) ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l9 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← l7 sK2 sK3 X1 X0]
  have l11 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK3) ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) X0 X1]
    conv => enter [1]; rw [l10 sK2 sK3 X0 X1]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← l1 X2 X3 (X0 ◇ X1)]
  have l13 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 (X2 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [l1 X1 X2 X0]
  have l14 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h41761 X2 (X0 ◇ (X3 ◇ (X3 ◇ X1))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41761 X0 X1 X3]
  have l15 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l16 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h41761 X0 (sK1 ◇ (sK2 ◇ sK3)) (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2, 2, 2]; rw [l6 sK1 sK2 sK3]
  have l17 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1, 2]; rw [l1 X2 X0 (X0 ◇ X1)]
  have l18 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1]; rw [h41761 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK3) ((sK2 ◇ sK3) ◇ X0)]
  have l19 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = ((X0 ◇ (X2 ◇ (X2 ◇ X1))) ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41761 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X2 ◇ (X2 ◇ X1))) X3]
  have l20 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41761 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2)))]
  have l21 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ X2))]
  have l22 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X0 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l19 X0 X1 X3 X2]
    conv => enter [1]; rw [← l1 X0 X3 (X0 ◇ (X2 ◇ (X2 ◇ X1)))]
  have l23 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1]; rw [l18 sK1 X0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) ((sK2 ◇ sK3) ◇ X0)]
  have l24 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l17 X2 X1 X0]
    conv => enter [1]; rw [l12 X2 (X0 ◇ X1) X2 X0]
  have l25 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3)))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l16 X0 sK1 sK2 sK3]
    conv => enter [1, 2, 2]; rw [← l1 (sK2 ◇ sK3) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK2 ◇ sK3))]
  have l26 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l15 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 (X1 ◇ X2) (X0 ◇ X1)]
  have l27 : ∀ X2 X1 X0 X3 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1]; rw [← l14 X2 X0 X3 X1]
  have l28 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
  have l29 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X3 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l22 X0 X1 X3 X2]
  have l30 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1]; rw [l23 sK1 X0 sK2 sK3]
    conv => enter [1]; rw [← l1 (sK2 ◇ sK3) X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l31 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l25 X0 sK1 sK2 sK3]
    conv => enter [1, 2, 2]; rw [l11 sK2 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK2 ◇ sK3))]
  have l32 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l26 X3 X2 X3 X1]
    conv => enter [1]; rw [← l13 X3 X1 (X1 ◇ X2) X3]
  have l33 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l28 X0 X1 X2 X3]
    conv => enter [1]; rw [← l24 X0 (X3 ◇ (X3 ◇ X2)) X1]
  have l34 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X3)) = (X0 ◇ (X3 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l29 X0 X1 X3 X0]
    conv => enter [1, 2]; rw [← l27 X3 X1 X0 X0]
  have l35 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l31 X0 sK1 sK2 sK3]
    conv => enter [1, 2, 2]; rw [← l30 sK1 (sK1 ◇ (sK2 ◇ sK3)) sK2 sK3]
  have l36 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l32 X0 X2 X0]
    conv => enter [1]; rw [← l33 X0 X1 X2 X0]
  have l37 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [h41761 X0 (sK2 ◇ sK3) sK1]
    conv => enter [1]; rw [← l35 X0 sK1 sK2 sK3]
  have l38 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l1 sK2 sK0 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l37 sK0 sK2 sK3 sK1]
  have l39 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ ((sK2 ◇ sK3) ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l34 sK2 (sK2 ◇ sK3) sK0]
    conv => enter [1]; rw [← l38 sK1 sK2 sK3 sK0]
  have l40 : ∀ sK2 sK0 sK1 sK3 : G, (sK2 ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1 sK3
    conv => enter [1]; rw [l36 sK2 sK0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l39 sK2 sK3 sK0 sK1]
  have l41 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 X0]
    conv => enter [1, 2, 2]; rw [← l37 sK1 sK2 sK3 sK1]
  have l42 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l36 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [← l41 sK1 sK2 sK3 X0]
  have l43 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l37 sK1 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l37 sK1 sK2 sK3 sK1]
  have l44 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l37 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l42 sK1 sK2 sK3 X0]
  have l45 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l44 sK1 sK2 sK3 X0]
    conv => enter [1, 1]; rw [← l43 sK1 sK2 sK3]
  have l46 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l45 sK1 sK2 sK3 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l40 sK2 sK0 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [← l46 z x w y]
  conv => enter [1]; rw [l43 z x w]

theorem Equation43_4512_41761_implies_Equation42238 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41761 : Equation41761 G) : Equation42238 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK4) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK4) X0]
  have l3 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK4)) X0]
  have l4 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ (sK3 ◇ sK4)) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) (sK3 ◇ sK4)]
    conv => enter [1]; rw [← l2 sK2 sK3 sK4 (sK2 ◇ (sK3 ◇ sK4))]
  have l5 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ (sK3 ◇ sK4)) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) (sK3 ◇ sK4)]
    conv => enter [1]; rw [← l2 sK2 sK3 sK4 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
  have l6 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← l5 sK2 sK3 sK4]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) (sK3 ◇ sK4)]
  have l7 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK3 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← l4 sK2 sK3 sK4]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) (sK3 ◇ sK4)]
  have l8 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (sK2 ◇ ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
    conv => enter [1, 2]; rw [l6 sK2 sK3 sK4]
  have l9 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0)) = (((sK3 ◇ sK4) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) ◇ X0) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK4)) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) X0]
    conv => enter [1, 1]; rw [l6 sK2 sK3 sK4]
  have l10 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0)) = ((sK3 ◇ sK4) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0)) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l9 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK4) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) X0]
  have l11 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l8 sK2 sK3 sK4]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK4) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l12 X2 X0 X1]
  have l14 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l12 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
  have l18 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h41761 X2 (X0 ◇ (X3 ◇ (X3 ◇ X1))) X0]
    conv => enter [1, 2, 2, 2]; rw [← h41761 X0 X1 X3]
  have l19 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [h41761 X0 (sK2 ◇ (sK3 ◇ sK4)) (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1, 2, 2, 2]; rw [l7 sK2 sK3 sK4]
  have l20 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))))))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [h41761 X0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
    conv => enter [1, 2, 2, 2]; rw [l11 sK2 sK3 sK4]
  have l21 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41761 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l1 X1 X1 X0]
  have l22 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ ((sK3 ◇ sK4) ◇ X0))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [h41761 sK2 X0 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK3 ◇ sK4) ((sK3 ◇ sK4) ◇ X0)]
  have l23 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [h41761 sK2 X0 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0)]
  have l24 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [h41761 sK2 X0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0)]
  have l25 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41761 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [l0 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2)))]
  have l26 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l25 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ X2))]
  have l27 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [l24 sK2 X0 sK3 sK4]
    conv => enter [1]; rw [l17 sK2 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) X0]
  have l28 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [l23 sK2 X0 sK3 sK4]
    conv => enter [1]; rw [l17 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) (sK2 ◇ (sK3 ◇ sK4)) X0]
  have l29 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = (sK2 ◇ ((sK3 ◇ sK4) ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [l22 sK2 X0 sK3 sK4]
    conv => enter [1]; rw [l17 sK2 (sK2 ◇ (sK3 ◇ sK4)) (sK3 ◇ sK4) X0]
  have l30 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))))))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [l20 X0 sK2 sK3 sK4]
    conv => enter [1, 2]; rw [l17 X0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) (sK2 ◇ (sK3 ◇ sK4)) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
  have l31 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (X0 ◇ ((sK3 ◇ sK4) ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [l19 X0 sK2 sK3 sK4]
    conv => enter [1, 2]; rw [l17 X0 (sK2 ◇ (sK3 ◇ sK4)) (sK3 ◇ sK4) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
  have l32 : ∀ X2 X1 X0 X3 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1]; rw [← l18 X2 X0 X3 X1]
  have l33 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l26 X0 X1 X2 X3]
  have l34 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0)) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [l27 sK2 X0 sK3 sK4]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0)]
  have l35 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0)) = (sK2 ◇ X0) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0)]
    conv => enter [1]; rw [← l28 sK2 X0 sK3 sK4]
  have l36 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0)) = (sK2 ◇ X0) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK4) ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0)]
    conv => enter [1]; rw [← l29 sK2 X0 sK3 sK4]
  have l37 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (X0 ◇ (X0 ◇ ((sK3 ◇ sK4) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))))))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [l30 X0 sK2 sK3 sK4]
    conv => enter [1, 2, 2]; rw [l10 sK2 sK3 sK4 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
  have l38 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (X0 ◇ ((sK3 ◇ sK4) ◇ ((sK3 ◇ sK4) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))))))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [l31 X0 sK2 sK3 sK4]
    conv => enter [1, 2, 2, 2]; rw [l6 sK2 sK3 sK4]
  have l39 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l33 X0 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← l32 X0 X2 X1 X0]
  have l40 : ∀ X0 sK3 sK4 sK2 : G, (X0 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro X0 sK3 sK4 sK2
    conv => enter [1]; rw [l21 X0 (sK3 ◇ sK4) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
    conv => enter [1]; rw [← l37 X0 sK2 sK3 sK4]
  have l41 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [l38 X0 sK2 sK3 sK4]
    conv => enter [1]; rw [← h41761 X0 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) (sK3 ◇ sK4)]
  have l42 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) X0]
    conv => enter [1]; rw [← l40 X0 sK3 sK4 sK2]
  have l43 : ∀ sK3 sK4 X0 sK2 : G, ((sK3 ◇ sK4) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) := by
    intro sK3 sK4 X0 sK2
    conv => enter [1]; rw [h43 (sK3 ◇ sK4) X0]
    conv => enter [1]; rw [← l42 sK2 sK3 sK4 X0]
  have l44 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [h41761 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) X0 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
    conv => enter [1, 2]; rw [← l34 sK2 ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) sK3 sK4]
  have l45 : ∀ X1 X0 sK2 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ (sK2 ◇ X0))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h41761 X1 X0 (sK2 ◇ (sK2 ◇ (sK2 ◇ (X1 ◇ X1))))]
    conv => enter [1, 2, 2]; rw [← l34 sK2 X0 X1 X1]
  have l46 : ∀ sK2 sK3 sK4 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X1) = (sK2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 sK4 X1 X0
    conv => enter [1]; rw [h41761 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) X1 X0]
    conv => enter [1]; rw [← l34 sK2 (X0 ◇ (X0 ◇ X1)) sK3 sK4]
  have l47 : ∀ sK2 sK3 sK4 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X1) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 sK4 X1 X0
    conv => enter [1]; rw [l46 sK2 sK3 sK4 X1 X0]
    conv => enter [1]; rw [← l39 X0 sK2 X1]
  have l48 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) = (sK2 ◇ (((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l44 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [← l1 sK2 ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
  have l49 : ∀ sK2 sK3 sK4 X1 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X1) = (X0 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 sK4 X1 X0
    conv => enter [1, 1]; rw [l40 sK2 sK3 sK4 sK2]
    conv => enter [1]; rw [l47 sK2 sK3 sK4 X1 X0]
  have l50 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l48 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [l13 sK2 ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
  have l51 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l50 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [← l39 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) sK2 X0]
  have l52 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l51 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [← l1 sK2 X0 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
  have l53 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l52 sK2 sK3 sK4 X0]
    conv => enter [1, 2]; rw [← l41 X0 sK2 sK3 sK4]
  have l54 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) ◇ X0) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l3 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [← l53 sK2 sK3 sK4 X0]
  have l55 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1, 1]; rw [l40 sK2 sK3 sK4 sK2]
    conv => enter [1]; rw [← l54 sK2 sK3 sK4 X0]
  have l56 : ∀ sK3 sK4 X0 sK2 : G, ((sK3 ◇ sK4) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) := by
    intro sK3 sK4 X0 sK2
    conv => enter [1]; rw [l43 sK3 sK4 X0 sK2]
    conv => enter [1]; rw [← l55 sK2 sK3 sK4 X0]
  have l57 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ ((sK3 ◇ sK4) ◇ X0)) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [← l35 sK2 sK3 sK4 X0]
    conv => enter [1, 2]; rw [← l43 sK3 sK4 X0 sK2]
  have l58 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = ((sK3 ◇ sK4) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [l57 sK2 X0 sK3 sK4]
    conv => enter [1]; rw [← l1 (sK3 ◇ sK4) X0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
  have l59 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ X0) = ((sK3 ◇ sK4) ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1]; rw [l58 sK2 X0 sK3 sK4]
    conv => enter [1, 2]; rw [← l40 X0 sK3 sK4 sK2]
  have l60 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK4)) ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0)]
    conv => enter [1, 2]; rw [l36 sK2 sK3 sK4 X0]
  have l61 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0)) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l49 sK2 sK3 sK4 X0 sK2]
    conv => enter [1]; rw [← l60 sK2 sK3 sK4 X0]
  have l62 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l61 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [← l1 (sK2 ◇ (sK3 ◇ sK4)) X0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
  have l63 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = ((sK3 ◇ sK4) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l62 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [← l56 sK3 sK4 (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) sK2]
  have l64 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = ((sK3 ◇ sK4) ◇ (X0 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l63 sK2 sK3 sK4 X0]
    conv => enter [1, 2]; rw [← l40 X0 sK3 sK4 sK2]
  have l65 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = (sK2 ◇ X0) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l64 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [← l59 sK2 X0 sK3 sK4]
  have l66 : ∀ sK3 sK4 X0 sK2 : G, ((sK3 ◇ sK4) ◇ X0) = (sK2 ◇ X0) := by
    intro sK3 sK4 X0 sK2
    conv => enter [1]; rw [l56 sK3 sK4 X0 sK2]
    conv => enter [1]; rw [l65 sK2 sK3 sK4 X0]
  have l67 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK2 ◇ X0) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [h43 X0 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1]; rw [l65 sK2 sK3 sK4 X0]
  have l68 : ∀ sK2 sK3 sK4 X1 X0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ (X1 ◇ X0)) = (X1 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK4 X1 X0
    conv => enter [1]; rw [l12 (sK2 ◇ (sK3 ◇ sK4)) X1 X0]
    conv => enter [1, 2]; rw [l65 sK2 sK3 sK4 X0]
  have l69 : ∀ sK2 sK3 sK4 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [l49 sK2 sK3 sK4 X0 X1]
    conv => enter [1]; rw [← l68 sK2 sK3 sK4 X1 X0]
  have l70 : ∀ sK2 sK3 sK4 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = ((sK3 ◇ sK4) ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [l69 sK2 sK3 sK4 X0 X1]
    conv => enter [1]; rw [← l56 sK3 sK4 (X1 ◇ X0) sK2]
  have l71 : ∀ sK2 sK3 sK4 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ X0) = (sK2 ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [l70 sK2 sK3 sK4 X0 X1]
    conv => enter [1]; rw [l66 sK3 sK4 (X1 ◇ X0) sK2]
  have l72 : ∀ sK3 sK4 X0 sK2 X1 : G, ((sK3 ◇ sK4) ◇ X0) = (sK2 ◇ (X1 ◇ X0)) := by
    intro sK3 sK4 X0 sK2 X1
    conv => enter [1]; rw [l56 sK3 sK4 X0 sK2]
    conv => enter [1]; rw [l71 sK2 sK3 sK4 X0 X1]
  have l73 : ∀ sK2 X0 X1 : G, (sK2 ◇ X0) = (sK2 ◇ (X1 ◇ X0)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l66 sK2 sK2 X0 sK2]
    conv => enter [1]; rw [l72 sK2 sK2 X0 sK2 X1]
  have l74 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK2 ◇ (X0 ◇ sK4)) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1, 2]; rw [← l73 sK2 sK4 sK3]
    conv => enter [1]; rw [l12 X0 sK2 sK4]
  have l75 : ∀ X0 sK2 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK2 ◇ sK4) := by
    intro X0 sK2 sK3 sK4
    conv => enter [1]; rw [l74 X0 sK2 sK3 sK4]
    conv => enter [1]; rw [← l73 sK2 sK4 X0]
  have l76 : ∀ sK2 sK3 sK4 X0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [← l73 sK2 sK4 sK3]
    conv => enter [1]; rw [← l75 X0 sK2 sK3 sK4]
  have l77 : ∀ sK2 sK3 sK4 X0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK2 ◇ X0) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l76 sK2 sK3 sK4 X0]
    conv => enter [1]; rw [l67 X0 sK2 sK3 sK4]
  have l78 : ∀ X0 X1 sK2 sK3 sK4 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro X0 X1 sK2 sK3 sK4
    conv => enter [1]; rw [h41761 X0 X1 sK2]
    conv => enter [1, 2, 2, 2]; rw [← l77 sK2 sK3 sK4 X1]
  have l79 : ∀ X0 X1 sK2 sK3 sK4 : G, (X0 ◇ X1) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 X1 sK2 sK3 sK4
    conv => enter [1]; rw [l78 X0 X1 sK2 sK3 sK4]
    conv => enter [1]; rw [← l45 X0 (sK2 ◇ (sK3 ◇ sK4)) sK2]
  have l80 : ∀ X0 X1 sK2 sK3 sK4 : G, (X0 ◇ X1) = (sK2 ◇ (sK3 ◇ sK4)) := by
    intro X0 X1 sK2 sK3 sK4
    conv => enter [1]; rw [l79 X0 X1 sK2 sK3 sK4]
    conv => enter [1]; rw [← l76 sK2 sK3 sK4 X0]
  have l81 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK3 ◇ sK4)) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l80 sK0 sK1 sK2 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [l81 x y z w u]
  conv => enter [1]; rw [l40 z w u z]

theorem Equation43_4512_41761_implies_Equation41747 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41761 : Equation41761 G) : Equation41747 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK1 ◇ sK2)]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 (sK1 ◇ sK2)]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1, 2]; rw [l4 sK1 sK2]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← l0 X2 X3 (X0 ◇ X1)]
  have l7 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 (X2 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 X2 X0]
  have l8 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h41761 X0 ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 sK1 sK2]
  have l10 : ∀ X1 X0 sK1 sK2 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)))) := by
    intro X1 X0 sK1 sK2 sK0
    conv => enter [1]; rw [h41761 X1 (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 sK1 sK2 X0]
  have l11 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h41761 X0 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l4 sK1 sK2]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41761 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l13 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1, 2]; rw [l0 X2 X0 (X0 ◇ X1)]
  have l14 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41761 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2)))]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ X2))]
  have l16 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l13 X2 X1 X0]
    conv => enter [1]; rw [l6 X2 (X0 ◇ X1) X2 X0]
  have l17 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ sK2) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l12 X0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l11 X0 sK2 sK1]
  have l18 : ∀ X1 X0 sK1 sK2 sK0 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))) := by
    intro X1 X0 sK1 sK2 sK0
    conv => enter [1]; rw [l10 X1 X0 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l19 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK2))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l9 X0 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK2]
  have l20 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l8 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l0 X0 (X1 ◇ X2) (X0 ◇ X1)]
  have l21 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l22 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l19 X0 sK1 sK2 X0]
    conv => enter [1]; rw [← l18 X0 sK2 sK1 sK2 X0]
  have l23 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l20 X3 X2 X3 X1]
    conv => enter [1]; rw [← l7 X3 X1 (X1 ◇ X2) X3]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
    conv => enter [1]; rw [← l16 X0 (X3 ◇ (X3 ◇ X2)) X1]
  have l25 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l22 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l26 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l23 X0 X2 X0]
    conv => enter [1]; rw [← l24 X0 X1 X2 X0]
  have l27 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l25 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l17 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l28 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l26 X0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l27 X0 sK1 sK2]
  have l29 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l28 X0 sK1 sK2]
    conv => enter [1]; rw [← l26 X0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l30 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l17 X0 sK1 sK2]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l17 sK1 sK1 sK2]
    conv => enter [1]; rw [l29 sK1 sK1 sK2]
  have l32 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l30 sK1 sK2 X0]
    conv => enter [1]; rw [← l26 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l33 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l29 sK1 sK1 sK2]
    conv => enter [1]; rw [← l32 sK1 sK2 X0]
  have l34 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  have l35 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l33 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 (sK1 ◇ sK2) X0 X1]
  have l36 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l26 X1 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l35 sK1 sK2 X1 X0]
  have l37 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [l34 sK1 sK2 sK0]
  have l38 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ X0) = (sK1 ◇ sK2) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l36 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← l31 sK1 sK2]
  have l39 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l38 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l37 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l38 x y y z]
  conv => enter [1]; rw [l39 y z x]

theorem Equation43_4512_41761_implies_Equation41763 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41761 : Equation41761 G) : Equation41763 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK2 ◇ sK3)) X0]
  have l2 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l3 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK3) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) sK3]
    conv => enter [1]; rw [← l2 sK2 sK3 (sK2 ◇ sK3)]
  have l4 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ sK3) = (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK3)) sK3]
    conv => enter [1, 2]; rw [l3 sK2 sK3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← l0 X2 X3 (X0 ◇ X1)]
  have l6 : ∀ sK2 X0 sK3 : G, (sK2 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l0 sK2 sK3 X0]
  have l7 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X0)) = (X3 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 (X2 ◇ X0) X1]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 X2 X0]
  have l8 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41761 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ sK3)))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [h41761 X0 ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1 sK2 sK3]
  have l10 : ∀ X1 X0 sK2 sK3 sK1 : G, (X1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = (X1 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X0)))) := by
    intro X1 X0 sK2 sK3 sK1
    conv => enter [1]; rw [h41761 X1 (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK1 sK2 sK3 X0]
  have l11 : ∀ X0 sK3 sK2 : G, (X0 ◇ sK3) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK3 sK2
    conv => enter [1]; rw [h41761 X0 sK3 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2, 2, 2]; rw [l3 sK2 sK3]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41761 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l13 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41761 X2 X1 X0]
    conv => enter [1, 2]; rw [l0 X2 X0 (X0 ◇ X1)]
  have l14 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41761 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ (X3 ◇ X2)))]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X3 ◇ X2))]
  have l16 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l13 X2 X1 X0]
    conv => enter [1]; rw [l5 X2 (X0 ◇ X1) X2 X0]
  have l17 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X0 ◇ sK3) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l12 X0 (sK2 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l11 X0 sK3 sK2]
  have l18 : ∀ X1 X0 sK2 sK3 sK1 : G, (X1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ X0))) := by
    intro X1 X0 sK2 sK3 sK1
    conv => enter [1]; rw [l10 X1 X0 sK2 sK3 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) X0]
  have l19 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) ◇ sK3))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [l9 X0 sK2 sK3 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) sK3]
  have l20 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l8 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l0 X0 (X1 ◇ X2) (X0 ◇ X1)]
  have l21 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l22 : ∀ X0 sK2 sK3 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l19 X0 sK2 sK3 X0]
    conv => enter [1]; rw [← l18 X0 sK3 sK2 sK3 X0]
  have l23 : ∀ X3 X2 X1 : G, (X3 ◇ X2) = (X3 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X1
    conv => enter [1]; rw [l20 X3 X2 X3 X1]
    conv => enter [1]; rw [← l7 X3 X1 (X1 ◇ X2) X3]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
    conv => enter [1]; rw [← l16 X0 (X3 ◇ (X3 ◇ X2)) X1]
  have l25 : ∀ X0 sK2 sK3 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l22 X0 sK2 sK3]
    conv => enter [1, 2]; rw [h43 sK3 (sK2 ◇ (sK2 ◇ sK3))]
  have l26 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l23 X0 X2 X0]
    conv => enter [1]; rw [← l24 X0 X1 X2 X0]
  have l27 : ∀ X0 sK2 sK3 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l25 X0 sK2 sK3]
    conv => enter [1, 2]; rw [← l17 (sK2 ◇ (sK2 ◇ sK3)) sK2 sK3]
  have l28 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l26 X0 (sK2 ◇ (sK2 ◇ sK3)) (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [← l27 X0 sK2 sK3]
  have l29 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l28 X0 sK2 sK3]
    conv => enter [1]; rw [← l26 X0 (sK2 ◇ sK3) (sK2 ◇ sK3)]
  have l30 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l6 X0 sK2 sK3]
    conv => enter [1, 2]; rw [← l17 X0 sK2 sK3]
  have l31 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l2 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← l17 X0 sK2 sK3]
  have l32 : ∀ sK2 sK3 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l17 sK2 sK2 sK3]
    conv => enter [1]; rw [l29 sK2 sK2 sK3]
  have l33 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l31 sK2 sK3 X0]
    conv => enter [1]; rw [← l26 sK2 (sK2 ◇ (sK2 ◇ sK3)) X0]
  have l34 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l30 X0 sK2 sK3]
    conv => enter [1]; rw [← l26 sK2 (sK2 ◇ (sK2 ◇ sK3)) X0]
  have l35 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← l29 sK2 sK2 sK3]
    conv => enter [1]; rw [← l33 sK2 sK3 X0]
  have l36 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← l29 sK2 sK2 sK3]
    conv => enter [1]; rw [← l34 X0 sK2 sK3]
  have l37 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l36 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l32 sK2 sK3]
  have l38 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l32 sK2 sK3]
    conv => enter [1]; rw [l37 sK2 sK3 sK1]
  have l39 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l36 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l38 sK2 sK3 sK1]
  have l40 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l32 sK2 sK3]
    conv => enter [1]; rw [l39 sK2 sK3 sK1]
  have l41 : ∀ sK2 sK3 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l35 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 (sK2 ◇ sK3) X0 X1]
  have l42 : ∀ X1 X0 sK2 sK3 : G, (X1 ◇ X0) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 sK2 sK3
    conv => enter [1]; rw [l26 X1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l41 sK2 sK3 X1 X0]
  have l43 : ∀ X1 X0 sK2 sK3 : G, (X1 ◇ X0) = (sK2 ◇ sK3) := by
    intro X1 X0 sK2 sK3
    conv => enter [1]; rw [l42 X1 X0 sK2 sK3]
    conv => enter [1]; rw [← l32 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l43 x y z w]
  conv => enter [1]; rw [l40 z w x]

theorem Equation43_4512_41747_implies_Equation38 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ sK1) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ sK1) X1]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l7 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l6 X1 X1 X0]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h41747 X0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41747 X0 X0 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41747 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ sK1) X0]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l7 X2 X0 X1]
    conv => enter [1]; rw [← l8 X2 X1 (X0 ◇ X0)]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [l6 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 (X0 ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [← h41747 (sK0 ◇ sK1) X0 sK0]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 (sK0 ◇ sK1)]
  have l16 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ sK1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l12 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l15 sK0 sK1 X0]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 (X1 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 X1]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l17 sK0 sK0 X1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l19 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l20 x y]

theorem Equation43_4512_41747_implies_Equation41805 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1 (X0 ◇ X0)]
  intro x y z w u
  conv => enter [1]; rw [l3 x y (y ◇ (z ◇ (w ◇ u)))]

theorem Equation43_4512_41747_implies_Equation41882 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1 (X0 ◇ X0)]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_41747_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation42405 G := by
  have l0 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK4 sK5 X0 : G, ((sK4 ◇ sK5) ◇ X0) = (sK4 ◇ (X0 ◇ sK5)) := by
    intro sK4 sK5 X0
    conv => enter [1]; rw [← h4512 sK4 sK5 X0]
    conv => enter [1, 2]; rw [h43 sK5 X0]
  have l3 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK2 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l1 X1 X1 X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1]; rw [← l5 X2 X1 (X0 ◇ X0)]
  have l7 : ∀ sK6 sK3 sK1 sK2 sK0 X0 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK6 sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l6 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6 X0]
  have l8 : ∀ sK4 sK5 X0 : G, (sK4 ◇ sK5) = ((sK4 ◇ sK5) ◇ X0) := by
    intro sK4 sK5 X0
    conv => enter [1]; rw [l6 sK4 sK5 (X0 ◇ sK5)]
    conv => enter [1]; rw [← l2 sK4 sK5 X0]
  have l9 : ∀ sK1 sK2 sK0 sK4 sK5 sK3 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK4 ◇ sK5)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK4) := by
    intro sK1 sK2 sK0 sK4 sK5 sK3
    conv => enter [1, 2]; rw [l6 sK4 sK5 sK3]
    conv => enter [1]; rw [← l3 sK3 sK1 sK2 sK0 sK4]
  have l10 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK4 ◇ sK5)) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l7 sK6 sK3 sK1 sK2 sK0 sK4]
    conv => enter [1]; rw [← l9 sK1 sK2 sK0 sK4 sK5 sK3]
  have l11 : ∀ sK6 sK3 sK1 sK2 sK0 sK4 sK5 : G, (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK4 ◇ sK5) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK6 sK3 sK1 sK2 sK0 sK4 sK5
    conv => enter [1]; rw [l10 sK6 sK3 sK1 sK2 sK0 sK4 sK5]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) (sK4 ◇ sK5)]
  have l12 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK4 sK5 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l11 sK6 sK3 sK1 sK2 sK0 sK4 sK5]
  intro x y z w u v r
  conv => enter [1]; rw [l12 x y z w u v r]

theorem Equation43_4512_41747_implies_Equation41732 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l3 x y (x ◇ (x ◇ (x ◇ x)))]

theorem Equation43_4512_41747_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1 (X0 ◇ X0)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 (X1 ◇ sK0)]
    conv => enter [1]; rw [← l0 X1 sK0 sK0]
  have l5 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation43_4512_41747_implies_Equation41734 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1 (X0 ◇ X0)]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l4 x z y]

theorem Equation43_4512_41747_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l9 X2 X0 X1]
    conv => enter [1]; rw [← l10 X2 X1 (X0 ◇ X0)]
  have l12 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l11 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) X1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 (sK0 ◇ (sK0 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 sK0]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ sK2) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l14 sK0 sK1 X0]
  have l16 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation43_4512_41747_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation42233 G := by
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
  have l6 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1]; rw [← l7 X2 X1 (X0 ◇ X0)]
  have l9 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l8 sK0 sK3 X0]
  have l10 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ X0) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ (sK1 ◇ sK2)) X1]
    conv => enter [1]; rw [l8 sK1 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) X0]
  have l11 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 sK2]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l12 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
    conv => enter [1]; rw [← l10 X1 sK1 sK2 sK1]
  have l13 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l9 sK3 sK0 (X0 ◇ sK3)]
    conv => enter [1]; rw [l5 sK0 X0 sK3]
  have l14 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK0) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l9 sK3 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l11 sK1 sK2 sK0]
    conv => enter [1]; rw [← l14 sK1 sK3 sK0 sK2]
  have l16 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK3 sK0 sK1]
    conv => enter [1]; rw [← l15 sK1 sK2 sK3 sK0]
  have l17 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l16 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l17 z w x y]

theorem Equation43_4512_41747_implies_Equation41740 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1 (X0 ◇ X0)]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l4 x z y]

theorem Equation43_4512_41747_implies_Equation42222 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation42222 G := by
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
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1]; rw [← l5 X2 X1 (X0 ◇ X0)]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 (sK0 ◇ (sK1 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l8 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ X0) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l6 sK1 X0 (sK2 ◇ X1)]
    conv => enter [1]; rw [l0 sK1 sK2 X1]
  have l9 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l6 (sK1 ◇ sK1) X0 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK2]
  have l10 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [l8 sK1 sK1 X1 sK2]
  have l11 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [l9 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK2]
  have l12 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK2 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 X0 sK2]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [l14 x y z]
  conv => enter [1]; rw [l6 z (x ◇ x) (z ◇ (z ◇ (x ◇ x)))]

theorem Equation43_4512_41747_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation42237 G := by
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
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l10 X2 X0 X1]
    conv => enter [1]; rw [← l11 X2 X1 (X0 ◇ X0)]
  have l13 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l12 sK0 sK3 X0]
  have l14 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l12 sK1 X0 (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))]
    conv => enter [1]; rw [l9 sK1 X1 sK2]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l16 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1]
    conv => enter [1]; rw [l14 sK1 sK1 X1 sK2]
  have l17 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l13 sK3 sK0 (X0 ◇ sK3)]
    conv => enter [1]; rw [l8 sK0 X0 sK3]
  have l18 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l13 sK3 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l15 sK1 sK2 sK0]
    conv => enter [1]; rw [← l18 sK1 sK3 sK0 sK2]
  have l20 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK3 sK0 sK1]
    conv => enter [1]; rw [← l19 sK1 sK2 sK3 sK0]
  have l21 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l16 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l20 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l21 z w x y]

theorem Equation43_4512_41747_implies_Equation41737 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation41737 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1 (X0 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [l3 x y (x ◇ (x ◇ (y ◇ z)))]

theorem Equation43_4512_41747_implies_Equation41741 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation41741 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1 (X0 ◇ X0)]
  intro x y z w
  conv => enter [1]; rw [l3 x y (x ◇ (x ◇ (z ◇ w)))]

theorem Equation43_4512_41747_implies_Equation42225 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation42225 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1]
    conv => enter [1]; rw [← l3 X2 X1 (X0 ◇ X0)]
  have l5 : ∀ sK1 X0 X1 sK2 sK3 : G, (sK1 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 X0 X1 sK2 sK3
    conv => enter [1]; rw [l4 sK1 X0 (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))]
    conv => enter [1]; rw [l1 sK1 X1 sK2 sK3]
  have l6 : ∀ sK1 sK2 sK3 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X1
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1]
    conv => enter [1]; rw [l5 sK1 sK1 X1 sK2 sK3]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK2]
    conv => enter [1]; rw [l4 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) sK0]
  intro x y z w
  conv => enter [1]; rw [← l7 z x w y]

theorem Equation43_4512_41747_implies_Equation42238 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation42238 G := by
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
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l10 X2 X0 X1]
    conv => enter [1]; rw [← l11 X2 X1 (X0 ◇ X0)]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 X0]
  have l14 : ∀ sK2 X0 X1 sK3 sK4 : G, (sK2 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 X0 X1 sK3 sK4
    conv => enter [1]; rw [l12 sK2 X0 (X1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))]
    conv => enter [1]; rw [l9 sK2 X1 sK3 sK4]
  have l15 : ∀ sK2 sK3 sK4 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l12 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) X0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))]
    conv => enter [1]; rw [l6 sK2 sK3 sK4]
  have l16 : ∀ sK2 sK3 sK4 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK2 sK3 sK4 X1
    conv => enter [1]; rw [l12 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) sK2]
    conv => enter [1]; rw [l14 sK2 sK2 X1 sK3 sK4]
  have l17 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 (X0 ◇ sK1)]
    conv => enter [1]; rw [l8 sK0 X0 sK1]
  have l18 : ∀ sK2 sK1 sK0 sK3 sK4 : G, (sK2 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) ◇ sK0) := by
    intro sK2 sK1 sK0 sK3 sK4
    conv => enter [1, 2]; rw [l13 sK1 sK0 (sK2 ◇ (sK3 ◇ sK4))]
    conv => enter [1]; rw [← l2 sK2 sK3 sK4 sK0]
  have l19 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l15 sK2 sK3 sK4 sK0]
    conv => enter [1]; rw [← l18 sK2 sK1 sK0 sK3 sK4]
  have l20 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = ((sK2 ◇ (sK3 ◇ sK4)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l17 sK1 sK0 sK2]
    conv => enter [1]; rw [← l19 sK2 sK3 sK4 sK1 sK0]
  have l21 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4)))) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l20 sK1 sK0 sK2 sK3 sK4]
    conv => enter [1]; rw [← l16 sK2 sK3 sK4 (sK2 ◇ (sK3 ◇ sK4))]
  intro x y z w u
  conv => enter [1]; rw [l21 x y z w u]

theorem Equation43_4512_41747_implies_Equation41761 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41747 : Equation41747 G) : Equation41761 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h41747 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h41747 X2 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41747 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1 (X0 ◇ X0)]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l4 x z y]

@[equational_result]
theorem Equation42238_implies_Equation38 (G : Type*) [Magma G] (h42238 : Equation42238 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation43_4512_42238_implies_Equation41805 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42238 : Equation42238 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
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

theorem Equation43_42238_implies_Equation41882 (G : Type*) [Magma G] (h43 : Equation43 G) (h42238 : Equation42238 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
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

theorem Equation43_42238_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h42238 : Equation42238 G) : Equation42405 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ sK4 sK5 sK6 sK3 sK1 sK2 sK0 : G, (sK4 ◇ sK5) = (sK6 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK5 sK6 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK4 sK5 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK6]
  intro x y z w u v r
  conv => enter [1]; rw [l1 x y z w u v r]

theorem Equation4512_42238_implies_Equation41732 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42238 : Equation42238 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_42238_implies_Equation42232 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42238 : Equation42238 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
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
theorem Equation42238_implies_Equation41734 (G : Type*) [Magma G] (h42238 : Equation42238 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

@[equational_result]
theorem Equation42238_implies_Equation42230 (G : Type*) [Magma G] (h42238 : Equation42238 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation43_42238_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h42238 : Equation42238 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ X1) = (sK3 ◇ sK0) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 sK3]
    conv => enter [1]; rw [h43 sK0 sK3]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l2 z w x y]

@[equational_result]
theorem Equation42238_implies_Equation41740 (G : Type*) [Magma G] (h42238 : Equation42238 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
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
theorem Equation42238_implies_Equation42222 (G : Type*) [Magma G] (h42238 : Equation42238 G) : Equation42222 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation43_42238_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h42238 : Equation42238 G) : Equation42237 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ X1) = (sK3 ◇ sK0) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 sK3]
    conv => enter [1]; rw [h43 sK0 sK3]
  have l2 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l3 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK2 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l3 w x y]
  conv => enter [1]; rw [l2 w z]

theorem Equation4512_42238_implies_Equation41737 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42238 : Equation42238 G) : Equation41737 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
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
theorem Equation42238_implies_Equation41741 (G : Type*) [Magma G] (h42238 : Equation42238 G) : Equation41741 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]
  conv => enter [1]; rw [l1 z w x]

@[equational_result]
theorem Equation42238_implies_Equation42225 (G : Type*) [Magma G] (h42238 : Equation42238 G) : Equation42225 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l0 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [l0 x y x w]
  conv => enter [1]; rw [l1 x w z]

theorem Equation4512_42238_implies_Equation41747 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42238 : Equation42238 G) : Equation41747 G := by
  have l0 : ∀ X0 X1 X5 X6 : G, (X0 ◇ X1) = (X5 ◇ X6) := by
    intro X0 X1 X5 X6
    conv => enter [1]; rw [h42238 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h42238 X5 X6 X0 X0 X0]
  have l1 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation42225_implies_Equation38 (G : Type*) [Magma G] (h42225 : Equation42225 G) : Equation38 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation42225_implies_Equation41805 (G : Type*) [Magma G] (h42225 : Equation42225 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation42225_implies_Equation41882 (G : Type*) [Magma G] (h42225 : Equation42225 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_42225_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42225 : Equation42225 G) : Equation42405 G := by
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
  have l5 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
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
  have l19 : ∀ sK2 sK0 X0 X2 : G, (sK2 ◇ sK0) = (X0 ◇ X2) := by
    intro sK2 sK0 X0 X2
    conv => enter [1]; rw [l6 sK2 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ sK2)))]
    conv => enter [1]; rw [← h42225 X0 X2 sK0 sK2]
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
theorem Equation42225_implies_Equation41732 (G : Type*) [Magma G] (h42225 : Equation42225 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (x ◇ x)))]

theorem Equation43_4512_42225_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42225 : Equation42225 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l5 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l7 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
  have l18 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42225 X0 X1 sK0 sK0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 X0]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42225 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l5 sK0 X0]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42225 X0 X1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l7 sK0 X0]
  have l21 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42225 X0 X1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X0]
  have l22 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42225 X0 X1 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK2 X0]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42225 X0 X1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l11 sK0 X0]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42225 X0 X1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l13 sK0 X0]
  have l25 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  have l26 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l24 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l23 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)]
  have l28 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l22 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l17 sK1 sK1 (sK1 ◇ sK2) X0]
  have l29 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l21 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l32 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l18 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l33 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l28 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l26 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ X0)) sK0]
  have l34 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l33 X0 X1 sK0 X0 X0]
    conv => enter [1]; rw [l27 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ X0)) sK0]
  have l35 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l34 X0 X1 sK0]
    conv => enter [1]; rw [l29 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0]
  have l36 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l35 X0 X1 sK0]
    conv => enter [1]; rw [l29 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0]
  have l37 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l36 X0 X1 sK0]
    conv => enter [1]; rw [l30 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) sK0]
  have l38 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l37 X0 X1 sK0]
    conv => enter [1]; rw [l31 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) sK0]
  have l39 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l38 X0 X1 sK0]
    conv => enter [1]; rw [l32 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) sK0]
  have l40 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l39 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0)]
  have l41 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l40 X0 X1 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l42 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l25 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l43 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [l42 sK0 sK0 X1]
  have l44 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK1 sK2 sK1]
    conv => enter [1]; rw [l41 sK1 sK1 sK0]
  have l45 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK0]
    conv => enter [1]; rw [← l43 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l45 x y z]

theorem Equation43_4512_42225_implies_Equation41734 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42225 : Equation42225 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ X0) = (sK0 ◇ (X0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
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
  have l6 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK1)) X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l8 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l11 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0 X1]
    conv => enter [1]; rw [l10 sK0 sK1 X0 X1]
  have l12 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l14 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l13 sK0 sK1 X0 X1]
  have l15 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X3 (X0 ◇ X1) X2]
  have l16 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h42225 X0 X1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l17 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h42225 X0 X1 sK0 sK2]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK2 X0]
  have l18 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h42225 X0 X1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 X0]
  have l19 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h42225 X0 X1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 X0]
  have l20 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h42225 X0 X1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1 X0]
  have l21 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l19 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK0 X0]
  have l22 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l18 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0 X0]
  have l23 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l17 X0 X1 sK0 X0]
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ ((sK0 ◇ X0) ◇ X0)) sK0 sK1]
  have l24 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l16 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 sK0 X0]
  have l25 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l21 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l26 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l22 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l27 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l23 X0 X1 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK0]
  have l28 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l24 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l29 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l27 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l25 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK0 sK1]
  have l30 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l29 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l26 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK1]
  have l31 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l30 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l28 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1]
  have l32 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l31 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 sK0]
  have l33 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l32 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  intro x y z
  conv => enter [1]; rw [l33 x y x z]

theorem Equation43_4512_42225_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42225 : Equation42225 G) : Equation42230 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK1)) X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l8 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l11 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0 X1]
    conv => enter [1]; rw [l10 sK0 sK1 X0 X1]
  have l12 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l14 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l13 sK0 sK1 X0 X1]
  have l15 : ∀ X0 X3 X2 X1 : G, (X0 ◇ X3) = (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X3 X2 X1
    conv => enter [1]; rw [h42225 X0 X3 X2 X1]
    conv => enter [1, 2, 2]; rw [h43 X2 (X0 ◇ X1)]
  have l16 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h42225 X0 X1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l17 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h42225 X0 X1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 X0]
  have l18 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h42225 X0 X1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 X0]
  have l19 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h42225 X0 X1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1 X0]
  have l20 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42225 X0 X1 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK2 X0]
  have l21 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l18 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK0 X0]
  have l22 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l17 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0 X0]
  have l23 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l16 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 sK0 X0]
  have l24 : ∀ X0 X3 sK1 sK2 X2 : G, (X0 ◇ X3) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X2))) := by
    intro X0 X3 sK1 sK2 X2
    conv => enter [1]; rw [l15 X0 X3 X2 X0]
    conv => enter [1]; rw [l20 X2 (X2 ◇ ((X0 ◇ X0) ◇ X2)) sK1 sK2]
  have l25 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l21 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l26 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l22 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l27 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l23 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ X0 X3 sK0 sK1 : G, (X0 ◇ X3) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1))) := by
    intro X0 X3 sK0 sK1
    conv => enter [1]; rw [l24 X0 X3 sK1 X0 X0]
    conv => enter [1]; rw [l19 sK1 (sK1 ◇ ((sK1 ◇ X0) ◇ X0)) sK0 sK1]
  have l29 : ∀ X0 X3 sK0 sK1 : G, (X0 ◇ X3) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK0))) := by
    intro X0 X3 sK0 sK1
    conv => enter [1]; rw [l28 X0 X3 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1)) sK0 sK1]
  have l30 : ∀ X0 X3 sK0 sK1 : G, (X0 ◇ X3) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 X3 sK0 sK1
    conv => enter [1]; rw [l29 X0 X3 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK0)) sK0 sK1]
  have l31 : ∀ sK0 sK1 X0 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (X0 ◇ X3) := by
    intro sK0 sK1 X0 X3
    conv => enter [1, 2]; rw [l26 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK1]
    conv => enter [1]; rw [← l30 X0 X3 sK0 sK1]
  have l32 : ∀ sK0 sK1 X0 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ X3) := by
    intro sK0 sK1 X0 X3
    conv => enter [1, 2]; rw [l27 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1]
    conv => enter [1]; rw [l31 sK0 sK1 X0 X3]
  have l33 : ∀ sK0 sK1 X0 X3 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (X0 ◇ X3) := by
    intro sK0 sK1 X0 X3
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l32 sK0 sK1 X0 X3]
  have l34 : ∀ sK0 sK1 X0 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ X3) := by
    intro sK0 sK1 X0 X3
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l33 sK0 sK1 X0 X3]
  intro x y z
  conv => enter [1]; rw [← l34 z x x y]

theorem Equation43_4512_42225_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42225 : Equation42225 G) : Equation42233 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  have l2 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l1 sK0 sK3 X0]
  have l3 : ∀ sK3 sK0 X0 X2 : G, (sK3 ◇ sK0) = (X0 ◇ X2) := by
    intro sK3 sK0 X0 X2
    conv => enter [1]; rw [l2 sK3 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ sK3)))]
    conv => enter [1]; rw [← h42225 X0 X2 sK0 sK3]
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

@[equational_result]
theorem Equation42225_implies_Equation41740 (G : Type*) [Magma G] (h42225 : Equation42225 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation43_4512_42225_implies_Equation42222 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42225 : Equation42225 G) : Equation42222 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  have l2 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ X0) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l1 sK1 X0 (sK2 ◇ X1)]
    conv => enter [1]; rw [l0 sK1 sK2 X1]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ sK2) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 X1 sK2]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l1 z (x ◇ x) (z ◇ (z ◇ (x ◇ x)))]

theorem Equation43_4512_42225_implies_Equation42237 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42225 : Equation42225 G) : Equation42237 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK2) X0]
  have l4 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l5 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42225 X0 X1 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK2 X0]
  have l6 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h42225 X0 X1 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [l4 sK1 X0 sK2]
  have l7 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h42225 X0 X1 sK2 sK2]
    conv => enter [1, 2, 2]; rw [← l2 sK2 X0]
  have l8 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  have l9 : ∀ X0 X1 sK2 : G, (X0 ◇ X1) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ X0)]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l5 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) sK1 sK2]
  have l11 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X1) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l10 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) sK2]
  have l12 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l11 X0 X1 sK2 sK1]
    conv => enter [1]; rw [l0 (sK2 ◇ sK2) (sK2 ◇ sK2) sK1]
  have l13 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l12 X0 X1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l14 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X1) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l13 X0 X1 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l15 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 sK0]
    conv => enter [1]; rw [l8 sK0 sK3 X0]
  have l16 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ X0) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l3 X1 sK1 sK2]
    conv => enter [1]; rw [l8 sK1 (X1 ◇ (sK2 ◇ sK2)) X0]
  have l17 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l8 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1]
    conv => enter [1]; rw [← l16 X1 sK1 sK2 sK1]
  have l18 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ sK0) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l15 sK3 sK0 sK3]
    conv => enter [1]; rw [l14 sK0 sK3 sK2 sK1]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l17 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l18 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [← l19 z w x y]

@[equational_result]
theorem Equation42225_implies_Equation41737 (G : Type*) [Magma G] (h42225 : Equation42225 G) : Equation41737 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (y ◇ z)))]

@[equational_result]
theorem Equation42225_implies_Equation41741 (G : Type*) [Magma G] (h42225 : Equation42225 G) : Equation41741 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [← l1 x z w y]

theorem Equation43_42225_implies_Equation42238 (G : Type*) [Magma G] (h43 : Equation43 G) (h42225 : Equation42225 G) : Equation42238 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h42225 X0 X1 X0 X0]
    conv => enter [1]; rw [← h42225 X0 X4 X0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h43 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK1 sK0 X0 X2 : G, (sK1 ◇ sK0) = (X0 ◇ X2) := by
    intro sK1 sK0 X0 X2
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ sK1)))]
    conv => enter [1]; rw [← h42225 X0 X2 sK0 sK1]
  have l3 : ∀ sK2 sK3 sK4 X0 X2 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ X2) := by
    intro sK2 sK3 sK4 X0 X2
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ sK4) (sK2 ◇ (sK2 ◇ (X0 ◇ sK2)))]
    conv => enter [1]; rw [← h42225 X0 X2 sK2 sK2]
  have l4 : ∀ sK1 sK0 sK2 sK3 sK4 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK3 ◇ sK4)) := by
    intro sK1 sK0 sK2 sK3 sK4
    conv => enter [1]; rw [l2 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l3 sK2 sK3 sK4 sK1 sK1]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]
  conv => enter [1]; rw [l0 z (w ◇ u) (z ◇ (z ◇ (w ◇ u)))]

theorem Equation43_4512_42223_implies_Equation41733 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42223 : Equation42223 G) : Equation41733 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK1)) X1]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h42223 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l7 X0 sK1 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK0 X0]
  have l9 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l8 X0 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ sK1) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l9 X0 sK1 sK0]
    conv => enter [1]; rw [l6 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y x]

theorem Equation43_4512_42223_implies_Equation41538 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42223 : Equation42223 G) : Equation41538 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42223 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_42223_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42223 : Equation42223 G) : Equation41529 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h42223 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation43_4512_42223_implies_Equation4276 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h42223 : Equation42223 G) : Equation4276 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X0) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h43 X1 (X2 ◇ X0)]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l5 X2 X0 X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h42223 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h42223 X0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l10 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l9 X0 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ X1)]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ X1)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h42223 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK1 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h42223 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l14 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l5 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l19 X0 sK0 sK1]
    conv => enter [1]; rw [← l11 X0 (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l21 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l11 (sK1 ◇ (sK1 ◇ sK1)) X0 sK0]
    conv => enter [1]; rw [← l18 X0 sK0 sK1]
  have l22 : ∀ sK1 X1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro sK1 X1 X0 sK0
    conv => enter [1]; rw [l6 (sK1 ◇ (sK1 ◇ sK1)) X1 X0]
    conv => enter [1, 1]; rw [l20 X0 sK1 sK0]
  have l23 : ∀ sK1 X1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK1 X1 X0 sK0
    conv => enter [1]; rw [l22 sK1 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l24 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l10 X1 X0 X1]
    conv => enter [1]; rw [l23 X1 X1 X0 sK0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l21 sK1 (sK1 ◇ sK1) sK0]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l24 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l26 sK1 sK1]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [l20 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [l20 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l32 x y]

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
theorem Equation41741_implies_Equation41805 (G : Type*) [Magma G] (h41741 : Equation41741 G) : Equation41805 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x y (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation41741_implies_Equation41882 (G : Type*) [Magma G] (h41741 : Equation41741 G) : Equation41882 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x y (z ◇ (w ◇ (u ◇ v)))]

theorem Equation43_4512_41741_implies_Equation42405 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41741 : Equation41741 G) : Equation42405 G := by
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
  have l3 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
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
theorem Equation41741_implies_Equation41732 (G : Type*) [Magma G] (h41741 : Equation41741 G) : Equation41732 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ (x ◇ (x ◇ x)))]

theorem Equation43_4512_41741_implies_Equation42232 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41741 : Equation41741 G) : Equation42232 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
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
theorem Equation41741_implies_Equation41734 (G : Type*) [Magma G] (h41741 : Equation41741 G) : Equation41734 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation43_4512_41741_implies_Equation42230 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41741 : Equation41741 G) : Equation42230 G := by
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
  have l8 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
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

theorem Equation43_4512_41741_implies_Equation42233 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41741 : Equation41741 G) : Equation42233 G := by
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
  have l6 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
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
theorem Equation41741_implies_Equation41740 (G : Type*) [Magma G] (h41741 : Equation41741 G) : Equation41740 G := by
  have l0 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation43_4512_41741_implies_Equation42222 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h41741 : Equation41741 G) : Equation42222 G := by
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
  have l4 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41741 X0 X1 X0 X0]
    conv => enter [1]; rw [← h41741 X0 X4 X0 X0]
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

end CommutativeSemigroup5
