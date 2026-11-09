import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_54163_implies_Equation53975 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54163 : Equation54163 G) : Equation53975 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← l1 X2 X3 (X0 ◇ X1)]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54163 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK0]
  have l10 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54163 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2]
  have l11 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54163 sK0 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2]
  have l12 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK2)]
  have l13 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK2) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK2]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l9 sK0 X0 sK1]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 sK1]
    conv => enter [1]; rw [← h54163 sK1 X0 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l12 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 sK0 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54163 sK0 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK0 sK1 sK2]
  have l19 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l15 sK1 sK2 X0]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
  have l24 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l25 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l24 sK1 sK0 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1 sK0]
    conv => enter [1]; rw [← l22 sK0 sK1 sK0]
  have l27 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l16 sK0 sK1 sK2]
  have l28 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l29 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l30 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [← l29 sK1 sK2 sK0]
  have l31 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l30 sK1 sK0 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l32 sK1 sK0]
  have l34 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54163 sK1 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l33 sK0 sK1]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l37 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l34 sK1 X0 sK0]
  have l38 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l37 sK1 sK0 X0]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK1 sK1]
    conv => enter [1]; rw [← l34 sK1 X0 sK0]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 sK2 sK0]
  have l41 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l41 sK1 sK0 sK2]
  have l43 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l38 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 X0 X0 sK1]
  have l44 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [l38 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ X0) X1]
  have l45 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l44 X1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l46 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l19 sK1 sK2 sK1]
    conv => enter [1]; rw [h54163 sK1 sK1 X0]
  have l47 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l46 sK1 sK2 X0]
    conv => enter [1]; rw [← l45 X0 sK0 sK1 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 sK0]
    conv => enter [1]; rw [l47 sK1 sK0 X0 sK0]
  have l49 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l50 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l43 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l51 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) = ((X0 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l43 sK0 sK1 X0]
    conv => enter [1]; rw [l0 X0 (X0 ◇ sK1) X1]
  have l52 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l51 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l1 X0 X1 (X0 ◇ sK1)]
  have l53 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((X1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l50 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ sK1) (X0 ◇ X1)]
  have l54 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l49 sK0 sK1 X1]
    conv => enter [1]; rw [l52 sK0 sK1 X1 X0]
  have l55 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l53 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l8 X0 (X1 ◇ sK1) X0 X1]
  have l56 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l43 sK0 sK1 sK0]
    conv => enter [1]; rw [l54 sK0 sK1 X0 X1]
  have l57 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l43 sK0 sK1 sK0]
    conv => enter [1]; rw [l55 sK0 sK1 X0 X1]
  have l58 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l57 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l56 sK0 sK1 sK0 X0]
  have l59 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54163 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l58 sK0 sK1 X0]
  have l60 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1, 2]; rw [l58 sK0 sK1 X0]
    conv => enter [1]; rw [← l59 X0 X1 sK0 sK1]
  have l61 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l58 sK0 sK1 X0]
    conv => enter [1]; rw [l60 X0 sK0 sK1 X1]
  have l62 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l1 X0 X0 X1]
    conv => enter [1]; rw [← l61 sK0 sK1 X1 X0]
  intro x y z
  conv => enter [1]; rw [l62 x y z x]
  conv => enter [1]; rw [← l43 z x z]

theorem Equation43_4512_54313_implies_Equation4271 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54313 : Equation54313 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54313 sK0 X0 X1]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l0 sK0 sK0 X0]
    conv => enter [1]; rw [h54313 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h54313 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [← h54313 sK0 sK0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l5 X0 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) sK0 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) sK0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l8 X0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l12 sK0 X0]
    conv => enter [1]; rw [l12 sK0 X1]
  have l16 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 (X0 ◇ X1) sK0 X2]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l16 X0 X1 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0 sK0]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l18 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l20 x y z]

theorem Equation43_4512_54313_implies_Equation54340 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54313 : Equation54313 G) : Equation54340 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l0 (sK1 ◇ (sK2 ◇ sK3)) sK0 X0]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK3 sK0]
  have l3 : ∀ sK1 X0 sK2 sK3 sK0 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l4 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← l0 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l5 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1, 2]; rw [h43 X0 sK0]
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [h54313 sK1 (sK2 ◇ sK3) sK0]
  have l7 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [h54313 sK1 (sK2 ◇ sK3) X0]
  have l8 : ∀ sK2 sK3 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l3 (sK2 ◇ sK3) sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h54313 sK1 (sK2 ◇ sK3) (sK2 ◇ (sK3 ◇ sK0))]
  have l9 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← l8 sK2 sK3 sK1 sK0]
  have l10 : ∀ sK2 sK3 sK1 sK0 X0 : G, ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [← l9 sK1 sK2 sK3 (X0 ◇ sK0) sK0]
    conv => enter [1]; rw [l5 sK1 sK2 sK3 X0 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l10 sK2 sK3 sK1 sK0 X0]
  have l13 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h54313 X0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l14 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l13 X0 sK1 sK2 sK3 sK0]
  have l15 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h54313 X0 sK1 X1]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3]
    conv => enter [1]; rw [← l15 sK1 sK2 sK3 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l16 x y z w]

theorem Equation43_4512_54313_implies_Equation54345 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54313 : Equation54313 G) : Equation54345 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ sK4) ◇ X0) = (sK3 ◇ (X0 ◇ sK4)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [← h4512 sK3 sK4 X0]
    conv => enter [1, 2]; rw [h43 sK4 X0]
  have l5 : ∀ sK3 sK1 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK0) X0]
  have l6 : ∀ sK3 sK1 sK0 sK4 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ sK4) = ((sK3 ◇ sK4) ◇ (sK1 ◇ sK0)) := by
    intro sK3 sK1 sK0 sK4
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ sK0) sK4]
    conv => enter [1]; rw [← l4 sK3 sK4 (sK1 ◇ sK0)]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54313 X0 X1 X2]
    conv => enter [1]; rw [← h54313 X0 X1 X3]
  have l9 : ∀ X0 sK3 sK1 sK0 X1 sK4 : G, (X0 ◇ ((sK3 ◇ (sK1 ◇ sK0)) ◇ X1)) = (X0 ◇ ((sK3 ◇ sK4) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK3 sK1 sK0 X1 sK4
    conv => enter [1]; rw [l8 X0 (sK3 ◇ (sK1 ◇ sK0)) X1 sK4]
    conv => enter [1, 2]; rw [l6 sK3 sK1 sK0 sK4]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l1 sK0 sK1 X1]
  have l11 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [l8 sK0 X0 sK1 X1]
  have l12 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK4 ◇ X0)) = (X1 ◇ (sK3 ◇ sK4)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l8 sK3 sK4 X0 X1]
    conv => enter [1]; rw [l2 sK3 sK4 X1]
  have l13 : ∀ sK3 sK1 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ X1)) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l5 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [l8 sK3 X0 (sK1 ◇ sK0) X1]
  have l14 : ∀ X1 sK3 sK4 sK1 sK0 : G, (X1 ◇ (sK3 ◇ sK4)) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ sK4) := by
    intro X1 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l12 sK3 sK4 X1 X1]
    conv => enter [1]; rw [← l13 sK3 sK1 sK0 sK4 X1]
  have l15 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ X1) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l11 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [l10 sK0 sK1 sK1 X1]
  have l16 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) = (sK3 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [← l2 sK3 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l15 sK1 sK0 X0]
  have l17 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l15 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X0 X1 (sK1 ◇ sK0)]
  have l18 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK0) ◇ X1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l15 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l7 (sK1 ◇ sK0) X0 X1]
  have l19 : ∀ X0 sK3 sK1 sK0 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro X0 sK3 sK1 sK0
    conv => enter [1]; rw [l16 X0 sK3 sK1 sK0]
    conv => enter [1]; rw [← l18 sK1 sK0 sK3 sK1]
  have l20 : ∀ X0 sK3 sK4 X1 : G, (X0 ◇ (sK3 ◇ sK4)) = (X1 ◇ (sK3 ◇ sK4)) := by
    intro X0 sK3 sK4 X1
    conv => enter [1]; rw [l14 X0 sK3 sK4 X0 X0]
    conv => enter [1]; rw [← l14 X1 sK3 sK4 X0 X0]
  have l21 : ∀ X0 X1 X2 sK3 sK1 sK0 sK4 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((sK3 ◇ (sK1 ◇ sK0)) ◇ sK4)) := by
    intro X0 X1 X2 sK3 sK1 sK0 sK4
    conv => enter [1]; rw [l8 X0 X1 X2 (sK3 ◇ sK4)]
    conv => enter [1, 2]; rw [l14 X1 sK3 sK4 sK1 sK0]
  have l22 : ∀ X0 X1 X2 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ ((sK3 ◇ sK4) ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 X2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l21 X0 X1 X2 sK3 sK1 sK0 sK4]
    conv => enter [1]; rw [l9 X0 sK3 sK1 sK0 sK4 sK4]
  have l23 : ∀ X0 X1 X2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro X0 X1 X2 sK1 sK0
    conv => enter [1]; rw [l22 X0 X1 X2 X0 X0 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 sK0 X0 (X0 ◇ X0)]
  have l24 : ∀ X0 X1 sK3 sK4 X2 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK4))) = (X2 ◇ (sK3 ◇ sK4)) := by
    intro X0 X1 sK3 sK4 X2
    conv => enter [1]; rw [h4512 X0 X1 (sK3 ◇ sK4)]
    conv => enter [1]; rw [l20 (X0 ◇ X1) sK3 sK4 X2]
  have l25 : ∀ sK2 sK3 sK4 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0 X1
    conv => enter [1]; rw [← l24 X0 X1 sK3 sK4 sK2]
  have l26 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l25 sK2 sK3 sK4 sK2 sK2]
    conv => enter [1]; rw [l23 sK2 sK2 (sK3 ◇ sK4) sK1 sK0]
  have l27 : ∀ sK2 sK3 sK4 X0 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 X0 sK1 sK0
    conv => enter [1]; rw [l26 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l19 X0 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l27 x y z x w u]

theorem Equation43_4512_54313_implies_Equation54388 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54313 : Equation54313 G) : Equation54388 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [h43 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK4 sK5 X0 : G, ((sK4 ◇ sK5) ◇ X0) = (sK4 ◇ (X0 ◇ sK5)) := by
    intro sK4 sK5 X0
    conv => enter [1]; rw [← h4512 sK4 sK5 X0]
    conv => enter [1, 2]; rw [h43 sK5 X0]
  have l4 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l0 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 (sK0 ◇ sK1) sK2 X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) sK2]
  have l6 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54313 X0 X1 X2]
    conv => enter [1]; rw [← h54313 X0 X1 X3]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 X1]
  have l9 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [l7 sK0 X0 sK1 X1]
  have l10 : ∀ sK4 sK5 X0 X1 : G, (sK4 ◇ (sK5 ◇ X0)) = (X1 ◇ (sK4 ◇ sK5)) := by
    intro sK4 sK5 X0 X1
    conv => enter [1]; rw [l7 sK4 sK5 X0 X1]
    conv => enter [1]; rw [l1 sK4 sK5 X1]
  have l11 : ∀ sK4 sK5 X0 X1 : G, ((sK4 ◇ sK5) ◇ X0) = (sK4 ◇ (X0 ◇ X1)) := by
    intro sK4 sK5 X0 X1
    conv => enter [1]; rw [l3 sK4 sK5 X0]
    conv => enter [1]; rw [l7 sK4 X0 sK5 X1]
  have l12 : ∀ X1 sK4 sK5 : G, (X1 ◇ (sK4 ◇ sK5)) = ((sK4 ◇ sK5) ◇ sK5) := by
    intro X1 sK4 sK5
    conv => enter [1]; rw [← l10 sK4 sK5 X1 X1]
    conv => enter [1]; rw [← l11 sK4 sK5 sK5 X1]
  have l13 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l9 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [l8 sK0 sK1 sK0 X1]
  have l14 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l6 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1 (X0 ◇ sK2)]
  have l15 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← l13 sK0 sK1 (X0 ◇ sK2)]
  have l16 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h43 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2]
  have l17 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l16 sK2 sK0 sK1]
    conv => enter [1]; rw [← l15 sK2 sK0 sK1 X0]
  have l18 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l16 sK2 sK0 sK1]
    conv => enter [1]; rw [← l14 X0 sK2 sK0 sK1]
  have l19 : ∀ sK2 sK0 sK1 sK4 sK5 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK4 ◇ sK5) ◇ sK5) := by
    intro sK2 sK0 sK1 sK4 sK5
    conv => enter [1]; rw [l17 sK2 sK0 sK1 (sK4 ◇ sK5)]
    conv => enter [1]; rw [l12 (sK2 ◇ (sK0 ◇ sK1)) sK4 sK5]
  have l20 : ∀ sK2 sK0 sK1 X0 sK4 sK5 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK4 ◇ sK5)) := by
    intro sK2 sK0 sK1 X0 sK4 sK5
    conv => enter [1]; rw [l19 sK2 sK0 sK1 sK4 sK5]
    conv => enter [1]; rw [← l12 X0 sK4 sK5]
  intro x y z w u v
  conv => enter [1]; rw [l20 x y z w u v]
  conv => enter [1]; rw [l18 w u v x]

theorem Equation43_4512_54313_implies_Equation54683 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54313 : Equation54313 G) : Equation54683 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK2 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK2]
  have l2 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [h43 (sK2 ◇ sK0) sK1]
  have l3 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l5 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l6 : ∀ sK5 sK6 X0 : G, ((sK5 ◇ sK6) ◇ X0) = (sK5 ◇ (X0 ◇ sK6)) := by
    intro sK5 sK6 X0
    conv => enter [1]; rw [← h4512 sK5 sK6 X0]
    conv => enter [1, 2]; rw [h43 sK6 X0]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l2 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l8 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54313 X0 X1 X2]
    conv => enter [1]; rw [← h54313 X0 X1 X3]
  have l11 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK2 sK0 X1
    conv => enter [1, 2]; rw [h43 sK2 sK0]
    conv => enter [1]; rw [l10 X0 sK0 sK2 X1]
  have l12 : ∀ X1 sK2 sK0 X0 X2 : G, (X1 ◇ ((sK2 ◇ sK0) ◇ X0)) = (X1 ◇ (sK0 ◇ X2)) := by
    intro X1 sK2 sK0 X0 X2
    conv => enter [1, 2]; rw [l5 sK2 sK0 X0]
    conv => enter [1]; rw [l10 X1 sK0 (X0 ◇ sK2) X2]
  have l13 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK2 ◇ sK0) ◇ X1)) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1, 2]; rw [h43 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l10 X0 (sK2 ◇ sK0) sK1 X1]
  have l14 : ∀ X1 sK1 sK2 sK0 X0 X2 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X1 ◇ ((sK2 ◇ sK0) ◇ X2)) := by
    intro X1 sK1 sK2 sK0 X0 X2
    conv => enter [1, 2]; rw [l7 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l10 X1 (sK2 ◇ sK0) (X0 ◇ sK1) X2]
  have l15 : ∀ X0 sK3 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1)) := by
    intro X0 sK3 sK1 sK2 sK0 X1
    conv => enter [1, 2]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l10 X0 (sK1 ◇ (sK2 ◇ sK0)) sK3 X1]
  have l16 : ∀ sK0 sK2 X0 X1 X2 : G, (sK0 ◇ (sK2 ◇ (X0 ◇ X1))) = ((sK2 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [l10 sK2 X0 X1 X2]
    conv => enter [1]; rw [l1 sK0 sK2 (X0 ◇ X2)]
  have l17 : ∀ sK5 sK6 X0 X1 : G, (sK5 ◇ (sK6 ◇ X0)) = ((sK5 ◇ sK6) ◇ X1) := by
    intro sK5 sK6 X0 X1
    conv => enter [1]; rw [l10 sK5 sK6 X0 X1]
    conv => enter [1]; rw [h4512 sK5 sK6 X1]
  have l18 : ∀ sK5 sK6 X0 X1 : G, ((sK5 ◇ sK6) ◇ X0) = (sK5 ◇ (X0 ◇ X1)) := by
    intro sK5 sK6 X0 X1
    conv => enter [1]; rw [l6 sK5 sK6 X0]
    conv => enter [1]; rw [l10 sK5 X0 sK6 X1]
  have l19 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l10 (sK2 ◇ sK0) sK1 X0 X1]
    conv => enter [1]; rw [l2 sK2 sK0 sK1 X1]
  have l20 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l10 (sK2 ◇ sK0) X0 sK1 X1]
  have l21 : ∀ sK3 sK1 sK2 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK3 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l8 sK3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l10 (sK1 ◇ (sK2 ◇ sK0)) X0 sK3 X1]
  have l22 : ∀ sK1 sK2 sK0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l20 sK1 sK2 sK0 sK1 sK1]
    conv => enter [1]; rw [l19 sK2 sK0 sK1 sK1 X1]
  have l23 : ∀ sK5 sK6 X1 : G, ((sK5 ◇ sK6) ◇ sK6) = ((sK5 ◇ sK6) ◇ X1) := by
    intro sK5 sK6 X1
    conv => enter [1]; rw [l18 sK5 sK6 sK6 sK5]
    conv => enter [1]; rw [l17 sK5 sK6 sK5 X1]
  have l24 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l20 sK1 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK2 X0 X1 sK1]
  have l25 : ∀ X1 sK3 sK1 sK2 sK0 X2 : G, (X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X1 ◇ ((sK2 ◇ sK0) ◇ X2)) := by
    intro X1 sK3 sK1 sK2 sK0 X2
    conv => enter [1]; rw [l15 X1 sK3 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [l14 X1 sK1 sK2 sK0 X1 X2]
  have l26 : ∀ X1 sK1 sK2 sK0 X2 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK0 ◇ X2)) := by
    intro X1 sK1 sK2 sK0 X2
    conv => enter [1]; rw [l13 X1 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [l12 X1 sK2 sK0 X1 X2]
  have l27 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [h54313 sK0 sK2 (X0 ◇ sK1)]
  have l28 : ∀ X1 sK1 sK2 sK0 sK3 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l13 X1 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [← l25 X1 sK3 sK1 sK2 sK0 X1]
  have l29 : ∀ X1 sK2 sK0 sK1 : G, (X1 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 sK2 sK0 sK1
    conv => enter [1]; rw [l11 X1 sK2 sK0 X1]
    conv => enter [1]; rw [← l26 X1 sK1 sK2 sK0 X1]
  have l30 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h54313 sK0 sK0 (sK0 ◇ sK2)]
  have l31 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l30 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l11 sK0 sK2 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l31 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h43 sK0 (sK2 ◇ sK0)]
  have l33 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l8 sK3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l22 sK1 sK2 sK0 (X0 ◇ sK3)]
  have l34 : ∀ sK3 sK1 sK2 sK0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) := by
    intro sK3 sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l22 sK1 sK2 sK0 sK3]
  have l35 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1)) = (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) ◇ X1) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← l0 (sK1 ◇ (sK2 ◇ sK0)) X0 X1]
    conv => enter [1, 1]; rw [← l22 sK1 sK2 sK0 X0]
  have l36 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l22 sK1 sK2 sK0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 (sK1 ◇ (sK2 ◇ sK0)) X1 X0]
  have l37 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK1) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l36 sK1 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l29 X1 sK2 sK0 sK1]
  have l38 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ X1)) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [l35 X0 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK0)) sK1 X1]
  have l39 : ∀ sK3 sK1 sK2 sK0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l34 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l32 sK1 sK2 sK0 sK1]
  have l40 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l33 sK3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l32 sK1 sK2 sK0 sK1]
  have l41 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [← l32 sK2 sK2 sK0 sK2]
    conv => enter [1]; rw [l37 sK2 sK2 sK0 X0 X1]
  have l42 : ∀ X0 sK1 sK2 sK0 X1 sK3 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1)) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK1) := by
    intro X0 sK1 sK2 sK0 X1 sK3
    conv => enter [1]; rw [l38 X0 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [← l21 sK3 sK1 sK2 sK0 sK1 X1]
  have l43 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l39 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [← l40 sK3 sK1 sK2 sK0 X0]
  have l44 : ∀ sK3 sK1 sK2 sK0 X0 X1 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l39 sK3 sK1 sK2 sK0]
    conv => enter [1]; rw [l41 sK2 sK0 X0 X1]
  have l45 : ∀ sK3 sK1 sK2 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK1) = (X0 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l42 X0 sK1 sK2 sK0 sK3 sK3]
    conv => enter [1, 2]; rw [l32 sK1 sK2 sK0 sK3]
  have l46 : ∀ X0 sK1 sK2 sK0 sK3 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK1) := by
    intro X0 sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l13 X0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l45 sK3 sK1 sK2 sK0 X0]
  have l47 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l43 sK3 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l46 X0 sK1 sK2 sK0 sK3]
  have l48 : ∀ X0 sK3 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK3 sK1 sK2 sK0 X1
    conv => enter [1, 2]; rw [l43 sK3 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [l4 X0 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) X1]
  have l49 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [l28 X0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l48 X0 X0 sK1 sK2 sK0 X1]
    conv => enter [1, 2]; rw [← l28 X0 sK1 sK2 sK0 X0]
  have l50 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [l29 X0 sK2 sK0 X0]
    conv => enter [1]; rw [l49 X0 X0 sK2 sK0 X1]
    conv => enter [1, 2]; rw [← l29 X0 sK2 sK0 X0]
  have l51 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l44 sK3 sK1 sK2 sK0 sK3 X0]
    conv => enter [1]; rw [← l50 X0 sK2 sK0 sK3]
  have l52 : ∀ X0 X1 X2 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l10 X0 X1 X2 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l47 X1 sK1 sK2 sK0 sK3]
  have l53 : ∀ X0 X1 X2 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 X2 sK1 sK2 sK0
    conv => enter [1]; rw [l52 X0 X1 X2 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l28 X0 sK1 sK2 sK0 X0]
  have l54 : ∀ X0 X1 X2 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X0 X1 X2 sK2 sK0
    conv => enter [1]; rw [l53 X0 X1 X2 X0 sK2 sK0]
    conv => enter [1]; rw [← l29 X0 sK2 sK0 X0]
  have l55 : ∀ X0 X1 X2 sK3 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 X2 sK3 sK1 sK2 sK0
    conv => enter [1]; rw [l54 X0 X1 X2 sK2 sK0]
    conv => enter [1]; rw [← l51 sK3 sK1 sK2 sK0 X0]
  have l56 : ∀ sK3 sK1 sK2 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK3 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l51 sK3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK0)]
  have l57 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [h43 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l56 sK3 sK1 sK2 sK0 sK1]
  have l58 : ∀ sK5 sK6 X0 X1 : G, ((sK5 ◇ sK6) ◇ sK6) = (X0 ◇ (X1 ◇ (sK5 ◇ sK6))) := by
    intro sK5 sK6 X0 X1
    conv => enter [1]; rw [l23 sK5 sK6 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 (sK5 ◇ sK6) X1 X0]
  have l59 : ∀ sK3 sK1 sK2 sK0 sK5 sK6 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK5 ◇ sK6) ◇ sK6) := by
    intro sK3 sK1 sK2 sK0 sK5 sK6
    conv => enter [1]; rw [l55 sK3 sK1 (sK2 ◇ sK0) sK3 sK3 sK5 sK6]
    conv => enter [1]; rw [← l58 sK5 sK6 sK3 sK3]
  have l60 : ∀ sK1 sK2 sK0 sK5 sK6 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK5 ◇ sK6) ◇ sK6) := by
    intro sK1 sK2 sK0 sK5 sK6
    conv => enter [1]; rw [l57 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l59 sK1 sK1 sK2 sK0 sK5 sK6]
  have l61 : ∀ sK1 sK2 sK0 sK5 sK6 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK5 ◇ sK6) ◇ X0) := by
    intro sK1 sK2 sK0 sK5 sK6 X0
    conv => enter [1]; rw [l60 sK1 sK2 sK0 sK5 sK6]
    conv => enter [1]; rw [l23 sK5 sK6 X0]
  have l62 : ∀ sK4 sK5 sK6 sK1 sK2 sK0 : G, (sK4 ◇ (sK5 ◇ sK6)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK5 sK6 sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK4 (sK5 ◇ sK6)]
    conv => enter [1]; rw [← l61 sK1 sK2 sK0 sK5 sK6 sK4]
  intro x y z w u v r
  conv => enter [1]; rw [l62 x y z u v r]
  conv => enter [1]; rw [l57 u v r w]

theorem Equation43_4512_54313_implies_Equation54312 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54313 : Equation54313 G) : Equation54312 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l4 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0 X1]
    conv => enter [1]; rw [h54313 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ X1)]
  have l5 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54313 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l4 X1 sK0 X0]
  have l6 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l5 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l6 X1 sK0 X0]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l7 sK0 X1 X0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 X1 X0]
  have l10 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 X1 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h54313 X0 X1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)]
    conv => enter [1, 2]; rw [← l10 sK0 X1 X0]
  have l13 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [← l0 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [h54313 (X0 ◇ X1) X2 X3]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54313 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l14 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l13 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l12 X0 X1 sK0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK0 sK0]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54313 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))]
    conv => enter [1]; rw [← l16 X1 X0 X2 X3]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
  have l21 : ∀ sK0 X1 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 X1 X0 X2 X3
    conv => enter [1]; rw [← l17 X0 X1 sK0]
    conv => enter [1]; rw [l19 X0 X1 X2 X3]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l22 sK0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) X0]
  have l25 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l1 sK1 sK2 X0]
    conv => enter [1]; rw [h54313 sK1 sK2 X0]
  have l26 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l25 X0 sK1 sK2]
    conv => enter [1]; rw [h54313 sK1 sK1 (sK1 ◇ sK2)]
  have l27 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← l26 X0 sK1 sK2]
  have l28 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l24 sK0 sK0]
    conv => enter [1]; rw [l27 sK0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l28 x x y z]
  conv => enter [1]; rw [← l24 x x]

theorem Equation43_4512_54313_implies_Equation54639 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54313 : Equation54313 G) : Equation54639 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l1 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l3 sK1 X0 X1]
  have l5 : ∀ X1 sK1 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [← l4 sK1 X0 X1]
    conv => enter [1]; rw [h54313 sK1 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l6 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h54313 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l5 X1 sK1 X0]
  have l7 : ∀ X1 sK1 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [← l6 sK1 X1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l7 X1 sK1 X0]
  have l9 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l8 sK1 X1 X0]
  have l10 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l9 sK1 X1 X0]
  have l11 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK1 X1 X0]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)]
    conv => enter [1, 2]; rw [← l11 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
  have l13 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← h54313 X0 X1 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)]
    conv => enter [1, 2]; rw [← l11 sK1 X1 X0]
  have l14 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [← l0 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [h54313 (X0 ◇ X1) X2 X3]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [← h54313 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l15 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l17 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l14 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))]
  have l18 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l13 X0 X1 sK1]
    conv => enter [1]; rw [← l12 sK1 X0]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l16 sK1 X0]
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) sK1 sK1]
  have l20 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54313 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))]
    conv => enter [1]; rw [← l17 X1 X0 X2 X3]
  have l21 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 X0]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK1) sK1]
  have l22 : ∀ sK1 X1 X0 X2 X3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK1 X1 X0 X2 X3
    conv => enter [1]; rw [← l18 X0 X1 sK1]
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
  have l23 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l21 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l24 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l23 sK1 X0]
  have l25 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l24 sK1 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) X0]
  have l26 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l2 X0 sK3 sK0]
    conv => enter [1]; rw [h54313 sK0 sK3 X0]
  have l27 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l26 X0 sK3 sK0]
    conv => enter [1]; rw [h54313 sK0 sK0 (sK0 ◇ sK3)]
  have l28 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l27 X0 sK3 sK0]
  have l29 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [← l25 sK1 sK1]
    conv => enter [1]; rw [l28 sK1 X0 sK3 sK0]
  have l30 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ sK0) ◇ X0) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l29 sK1 X0 sK3 sK0]
    conv => enter [1]; rw [h43 X0 (sK3 ◇ sK0)]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l30 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [h43 (sK3 ◇ sK0) sK2]
  intro x y z w
  conv => enter [1]; rw [← l31 w x y z]
  conv => enter [1]; rw [← l25 w w]

theorem Equation43_4512_54313_implies_Equation54315 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54313 : Equation54313 G) : Equation54315 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK1 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [← h54313 sK1 sK2 X0]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l0 X0 X1 sK2]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK1 sK2 X0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [h54313 sK1 X0 (sK1 ◇ sK2)]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l5 sK1 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 X0]
    conv => enter [1]; rw [← h54313 sK1 X0 X1]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0 sK3]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l9 x w y z]
  conv => enter [1]; rw [← l5 x w x]

theorem Equation43_4512_54162_implies_Equation53863 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54162 : Equation54162 G) : Equation53863 G := by
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
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l10 sK1 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h54162 X1 X0]
    conv => enter [1, 2, 2]; rw [h43 X1 X0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54162 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l17 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h54162 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54162 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l9 sK0 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [h54162 sK0 (sK0 ◇ sK1)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54162 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l13 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l31 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l17 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK1 ◇ sK1)]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l35 sK1 sK0]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l29 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l14 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l41 sK1 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ sK1) (sK0 ◇ sK1)]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK0]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l47 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l48 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l49 x y]

theorem Equation43_4512_54162_implies_Equation53860 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54162 : Equation54162 G) : Equation53860 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← h54162 X0 X1]
    conv => enter [1]; rw [← h54162 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← h54162 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← h54162 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l5 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X1) X1 X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [l0 X1 (X1 ◇ X1) X1]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l7 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← h54162 X1 X1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l11 X0 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X0) X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation43_4512_54162_implies_Equation4284 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54162 : Equation54162 G) : Equation4284 G := by
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
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [h54162 X0 (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [h54162 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h54162 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1 X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [← h54162 sK1 X0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 2]; rw [← h54162 X0 X1]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X1 ◇ X1) ◇ (X2 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← h54162 X0 X1]
    conv => enter [1]; rw [l1 X2 X0 (X1 ◇ X1)]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X1 (X2 ◇ X0)]
    conv => enter [1]; rw [← l10 X2 X0 X1]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1, 2]; rw [l1 (X1 ◇ X1) X1 X1]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l12 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [l1 X1 (X1 ◇ X1) X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0 X1]
    conv => enter [1]; rw [← l15 X0 X1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1]; rw [← l14 (X0 ◇ X1) X0 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X0) (X0 ◇ X1)]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1]; rw [l5 X0 (X0 ◇ X0) X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l21 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1]; rw [← l14 X1 X0 X0]
  have l22 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l7 X0 sK1]
    conv => enter [1]; rw [l21 X0 sK1]
  have l23 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l22 X0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ sK1) X0]
  have l24 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l23 X0 sK1]
    conv => enter [1]; rw [l8 sK1 X0]
  have l25 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l24 X0 sK1]
    conv => enter [1]; rw [← l1 X0 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l25 x y]

theorem Equation4512_54162_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54162 : Equation54162 G) : Equation53807 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54162 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation43_4512_53861_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53861 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l3 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 X2]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [← l6 x y x]

theorem Equation43_4512_53861_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53864 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l2 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation43_4512_53861_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53867 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ ((X0 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 1]; rw [l2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (X0 ◇ sK2) X1]
  have l4 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l3 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 X1]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l4 sK2 X0 X1]
  have l6 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l7 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h53861 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 X1]
  have l8 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1]; rw [l7 sK2 X0 X1]
  have l9 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l1 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l8 sK2 X0 X1]
  have l10 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l9 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l11 : ∀ sK2 X0 X2 X1 : G, ((sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ X2) = (X1 ◇ ((sK2 ◇ sK2) ◇ X2)) := by
    intro sK2 X0 X2 X1
    conv => enter [1, 1]; rw [l9 sK2 X0 X1]
    conv => enter [1]; rw [l0 (sK2 ◇ sK2) X1 X2]
  have l12 : ∀ X1 sK2 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ X2)) = (sK2 ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ X2)) := by
    intro X1 sK2 X2 X0
    conv => enter [1]; rw [← l11 sK2 X0 X2 X1]
    conv => enter [1]; rw [← h4512 sK2 (X0 ◇ (sK2 ◇ sK2)) X2]
  have l13 : ∀ X1 sK2 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ X2)) = (sK2 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X2))) := by
    intro X1 sK2 X2 X0
    conv => enter [1]; rw [l12 X1 sK2 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ sK2) X2]
  have l14 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l9 sK2 sK0 X1]
    conv => enter [1]; rw [l13 X1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [← l9 sK2 sK0 X1]
  have l15 : ∀ sK2 X0 sK0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK0 X1
    conv => enter [1]; rw [l5 sK2 X0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l14 X1 sK2 sK0 X0]
  have l16 : ∀ sK2 X1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [← l10 sK2 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l15 sK2 sK2 sK0 X1]
  have l17 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l9 sK2 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l16 sK2 X1 sK0]
  have l18 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l9 sK2 sK0 X0]
  have l19 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK2 sK0 X0]
  have l20 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l1 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK2 sK0 (X0 ◇ X1)]
  have l21 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK2 X0]
    conv => enter [1]; rw [← l17 sK2 sK0 sK0]
  have l22 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l19 X0 sK2 X0]
    conv => enter [1]; rw [← l19 X1 sK2 X0]
  have l23 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l1 X0 X1 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l21 sK0 sK2 (X0 ◇ X1)]
  have l24 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l22 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l25 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l24 sK0 sK2 X0 sK0]
  have l26 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h53861 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l20 X0 X0 sK2 sK0]
  have l27 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l26 X0 X1 sK2 sK0]
    conv => enter [1]; rw [l23 X0 sK2 sK0 sK2]
  have l28 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l27 X0 X1 sK2 sK0]
    conv => enter [1]; rw [← l25 sK0 sK2 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [l28 sK0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l29 x y z]
  conv => enter [1]; rw [l25 x z x]

theorem Equation43_4512_53861_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53868 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l1 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l2 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 X0]
  have l4 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK1) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 (sK3 ◇ sK0) X0]
  have l5 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l7 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l5 sK1 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation43_4512_53861_implies_Equation53874 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53874 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l5 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l6 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l5 sK1 X1 (X0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK2 X0]
  have l9 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 (sK1 ◇ sK2)]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK2 X0]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l9 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [l4 sK0 sK1 sK1 sK2]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l16 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 X0]
    conv => enter [1]; rw [← l11 sK1 sK2 X0]
  have l17 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 X0]
  have l18 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l19 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l18 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 (sK1 ◇ sK2)]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [← l19 sK1 sK0 sK2]
  have l21 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l17 sK1 sK2 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK0]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l22 sK1 sK2 sK0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← l21 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l24 x y z]
  conv => enter [1]; rw [l22 y z x]

theorem Equation43_4512_53861_implies_Equation53877 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53877 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l4 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l5 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h53861 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 X1]
  have l6 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1]; rw [l5 sK2 X0 X1]
  have l7 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l6 sK2 X0 X1]
  have l8 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l7 sK2 sK1 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) sK2 sK1]
  have l10 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 X0 sK2 sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 (sK0 ◇ sK1)]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2 sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation43_4512_53861_implies_Equation53890 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53890 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l4 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l0 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l5 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l6 : ∀ sK3 X1 sK0 X0 : G, (sK3 ◇ (sK3 ◇ X1)) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 X1 sK0 X0
    conv => enter [1]; rw [l5 sK3 X1 (X0 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← l3 sK3 sK0 X0]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK2 X0]
  have l8 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK3 ◇ (sK3 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [l5 sK3 sK0 X0]
  have l9 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l8 sK3 sK0 sK3]
    conv => enter [1]; rw [l5 sK3 sK3 (sK3 ◇ sK0)]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 (sK3 ◇ (sK3 ◇ sK0))]
  have l11 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l5 sK3 (sK3 ◇ sK0) sK3]
    conv => enter [1]; rw [l6 sK3 sK3 sK0 X0]
  have l12 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l9 sK3 sK0]
  have l13 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0]
  have l14 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1, 2]; rw [l12 sK3 sK0]
    conv => enter [1]; rw [l4 sK1 sK3 sK3 sK0]
  have l15 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1, 1]; rw [l12 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l16 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l15 sK3 sK0 X0]
    conv => enter [1]; rw [← l11 sK3 sK0 X0]
  have l17 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l12 sK3 sK0]
    conv => enter [1]; rw [← l16 sK3 sK0 X0]
  have l18 : ∀ sK3 X0 sK1 sK0 : G, (sK3 ◇ (sK3 ◇ X0)) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 X0 sK1 sK0
    conv => enter [1]; rw [l5 sK3 X0 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l14 sK1 sK3 sK0]
  have l19 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK3 ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK3 sK0]
    conv => enter [1]; rw [← l18 sK3 X0 sK1 sK0]
  have l20 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l5 sK3 sK0 sK3]
    conv => enter [1]; rw [← l19 sK1 sK3 sK0 sK3]
  have l21 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l20 sK3 sK0 sK1]
  have l22 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l17 sK3 sK0 X0]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l22 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l23 x y z w]
  conv => enter [1]; rw [l20 z w x]

theorem Equation43_4512_53861_implies_Equation53914 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53914 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l2 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h53861 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 X1]
  have l3 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1]; rw [l2 sK2 X0 X1]
  have l4 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l3 sK2 X0 X1]
  have l5 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK2 sK1 X0]
  have l6 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l5 X0 sK2 X0]
    conv => enter [1]; rw [← l5 X1 sK2 X0]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0 sK1]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l1 X0 X1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 X0]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l9 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X0]
  have l11 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l10 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l12 x y z]
  conv => enter [1]; rw [l8 y z y]

theorem Equation43_4512_53861_implies_Equation53915 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53915 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h43 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l3 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l5 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK2 sK1]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l7 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l8 : ∀ sK2 X1 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ X1)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK2 X1 sK3 sK0 X0
    conv => enter [1]; rw [l7 sK2 X1 (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l3 sK2 sK3 sK0 X0]
  have l9 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l6 sK2 sK1 sK2]
    conv => enter [1]; rw [l7 sK2 sK1 X0]
  have l10 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK2]
    conv => enter [1]; rw [l7 sK2 sK1 X0]
  have l11 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l2 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [l7 sK2 (sK3 ◇ sK0) X0]
  have l12 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [l7 sK2 sK2 (sK2 ◇ (sK3 ◇ sK0))]
  have l13 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l7 sK2 (sK2 ◇ (sK3 ◇ sK0)) sK2]
    conv => enter [1]; rw [← l10 sK1 sK2 sK2]
  have l14 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l7 sK2 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [← l9 sK2 sK1 sK2]
  have l15 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l7 sK2 (sK2 ◇ (sK3 ◇ sK0)) sK2]
    conv => enter [1]; rw [l8 sK2 sK2 sK3 sK0 X0]
  have l16 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l12 sK2 sK3 sK0]
  have l17 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l13 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ sK2) sK2]
  have l18 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [l16 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l19 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l18 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← l15 sK2 sK3 sK0 X0]
  have l20 : ∀ sK2 sK3 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [l19 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l17 sK2 sK3 sK0 sK1]
  have l21 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l14 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [← l20 sK2 sK3 sK0 X0 sK2]
  have l22 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l21 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l23 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [l7 X0 X1 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l22 sK2 sK3 sK0 X0]
  have l24 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [l23 X0 X1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l22 sK2 sK3 sK0 X0]
  have l25 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [← l24 X0 X1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l1 X0 X1 X0]
  have l26 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h43 sK1 sK2]
    conv => enter [1]; rw [← l25 sK2 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l26 x y z w]

theorem Equation43_4512_53861_implies_Equation53927 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53927 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK3 ◇ sK0))]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l4 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l5 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l6 : ∀ sK3 X1 sK0 X0 : G, (sK3 ◇ (sK3 ◇ X1)) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 X1 sK0 X0
    conv => enter [1]; rw [l5 sK3 X1 (X0 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← l3 sK3 sK0 X0]
  have l7 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK3 ◇ (sK3 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [l5 sK3 sK0 X0]
  have l8 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l7 sK3 sK0 sK3]
    conv => enter [1]; rw [l5 sK3 sK3 (sK3 ◇ sK0)]
  have l9 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l5 sK3 (sK3 ◇ sK0) sK3]
    conv => enter [1]; rw [l6 sK3 sK3 sK0 X0]
  have l10 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l8 sK3 sK0]
  have l11 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [l10 sK3 sK0]
    conv => enter [1]; rw [l4 sK2 sK3 sK3 sK0]
  have l12 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1, 1]; rw [l10 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l13 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l12 sK3 sK0 X0]
    conv => enter [1]; rw [← l9 sK3 sK0 X0]
  have l14 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l10 sK3 sK0]
    conv => enter [1]; rw [← l13 sK3 sK0 X0]
  have l15 : ∀ sK3 X0 sK2 sK0 : G, (sK3 ◇ (sK3 ◇ X0)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 X0 sK2 sK0
    conv => enter [1]; rw [l5 sK3 X0 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l11 sK2 sK3 sK0]
  have l16 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK2 sK3 sK0]
    conv => enter [1]; rw [← l15 sK3 X0 sK2 sK0]
  have l17 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l5 sK3 sK0 sK3]
    conv => enter [1]; rw [← l16 sK2 sK3 sK0 sK3]
  have l18 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l14 sK3 sK0 X0]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 sK0]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l18 sK3 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  intro x y z w
  conv => enter [1]; rw [l20 x y z w]
  conv => enter [1]; rw [l17 z w y]

theorem Equation43_4512_53861_implies_Equation53982 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53982 G := by
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
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l2 X2 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53861 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X1) X2]
  have l8 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l6 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 sK0 X2]
  have l9 : ∀ X1 sK3 sK0 X0 : G, (X1 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK3 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK3 sK0 X0
    conv => enter [1]; rw [← l1 sK3 (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← l6 sK0 X0 X1]
  have l10 : ∀ X1 sK3 sK0 X0 : G, (X1 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ sK3)) := by
    intro X1 sK3 sK0 X0
    conv => enter [1]; rw [l9 X1 sK3 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ sK0)) sK3]
  have l11 : ∀ sK0 X0 X1 sK3 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 sK3
    conv => enter [1]; rw [l7 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 sK3 sK0]
  have l12 : ∀ X1 sK3 sK0 X0 : G, (X1 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK3 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK3 sK0 X0
    conv => enter [1]; rw [l10 X1 sK3 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (sK0 ◇ sK0)) sK3]
  have l13 : ∀ X1 sK3 sK0 : G, (X1 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK3 sK0
    conv => enter [1]; rw [l12 X1 sK3 sK0 X1]
    conv => enter [1]; rw [l11 sK0 sK3 X1 sK3]
  have l14 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l13 sK3 sK3 sK0]
    conv => enter [1]; rw [← l13 X0 sK3 sK0]
  have l15 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l14 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l14 sK3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 (sK3 ◇ (sK0 ◇ sK0)) X0]
  have l17 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l15 sK3 sK0 X0 sK3]
  have l18 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l16 sK3 sK0 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) X0]
  have l19 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l16 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1 (sK0 ◇ sK0)]
  have l20 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h53861 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l19 X0 sK0 sK3 sK3]
  have l21 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l20 X0 X1 sK3 sK0]
    conv => enter [1]; rw [← l17 sK3 sK0 X0]
  have l22 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l21 X0 X1 sK3 sK0]
    conv => enter [1]; rw [l18 sK3 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l22 x y z w]
  conv => enter [1]; rw [← l18 z w z]

theorem Equation43_4512_53861_implies_Equation53983 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53983 G := by
  have l0 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l1 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l2 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK4 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK4 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK4 (sK4 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53861 X0 X1 X0]
    conv => enter [1]; rw [← h53861 X0 X3 X0]
  have l5 : ∀ sK2 X1 sK3 X0 : G, (sK2 ◇ (sK2 ◇ X1)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK2 X1 sK3 X0
    conv => enter [1]; rw [l4 sK2 X1 (X0 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l1 sK2 sK3 X0]
  have l6 : ∀ sK4 X1 sK1 sK0 X0 : G, (sK4 ◇ (sK4 ◇ X1)) = (sK4 ◇ ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK4 X1 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK4 X1 (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l3 sK4 sK1 sK0 X0]
  have l7 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l0 sK2 sK3 sK2]
    conv => enter [1]; rw [l4 sK2 sK3 X0]
  have l8 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK4) = (sK4 ◇ (sK4 ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l2 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [l4 sK4 (sK1 ◇ sK0) X0]
  have l9 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK4) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l8 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [l4 sK4 sK4 (sK4 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l7 sK2 sK3 sK2]
    conv => enter [1]; rw [l4 sK2 sK2 (sK2 ◇ sK3)]
  have l11 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK4 ◇ ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK4 (sK4 ◇ (sK1 ◇ sK0)) sK4]
    conv => enter [1]; rw [l6 sK4 sK4 sK1 sK0 X0]
  have l12 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l4 sK2 (sK2 ◇ sK3) sK2]
    conv => enter [1]; rw [l5 sK2 sK2 sK3 X0]
  have l13 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [h43 sK4 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l9 sK4 sK1 sK0]
  have l14 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l10 sK2 sK3]
  have l15 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK4 ◇ ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1, 1]; rw [l13 sK4 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK4 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l16 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l15 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← l11 sK4 sK1 sK0 X0]
  have l17 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l13 sK4 sK1 sK0]
    conv => enter [1]; rw [← l16 sK4 sK1 sK0 X0]
  have l18 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1, 1]; rw [l14 sK2 sK3]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK3)) X0]
  have l19 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l18 sK2 sK3 X0]
    conv => enter [1]; rw [← l12 sK2 sK3 X0]
  have l20 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l14 sK2 sK3]
    conv => enter [1]; rw [← l19 sK2 sK3 X0]
  have l21 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l17 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [h43 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l22 : ∀ sK2 sK4 sK1 sK0 sK3 : G, (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1, 2]; rw [l17 sK4 sK1 sK0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l1 sK2 sK3 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l23 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l20 sK2 sK3 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l22 sK2 sK4 sK1 sK0 sK3]
  have l24 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l23 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l21 sK4 sK1 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l24 x y z w u]

theorem Equation43_4512_53861_implies_Equation53859 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53859 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53861 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation43_4512_53861_implies_Equation54161 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation54161 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53861 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h53861 sK1 X1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X1]
  have l4 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [l3 sK1 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l6 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l4 sK1 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l6 sK1 sK0 X0]
  have l9 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l8 X0 sK1 X0]
    conv => enter [1]; rw [← l8 X1 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l9 X0 sK1 sK0]
  have l11 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0 sK0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 X0]
  have l15 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l14 sK0 sK1 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l7 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 X0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [← l18 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l19 x y]

theorem Equation43_4512_53861_implies_Equation53977 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation53977 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h53861 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l2 sK0 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l1 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1 (sK0 ◇ sK0)]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53861 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK0 X0 X0]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK0]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l11 X0 X1 sK0]
    conv => enter [1]; rw [l8 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l12 x y z]
  conv => enter [1]; rw [← l8 z z]

theorem Equation43_4512_53861_implies_Equation54163 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53861 : Equation53861 G) : Equation54163 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ ((X0 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 1]; rw [l2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (X0 ◇ sK2) X1]
  have l4 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l3 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 X1]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l4 sK2 X0 X1]
  have l6 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h53861 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 X1]
  have l7 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1]; rw [l6 sK2 X0 X1]
  have l8 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l1 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l7 sK2 X0 X1]
  have l9 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l8 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l10 : ∀ sK2 X0 X2 X1 : G, ((sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ X2) = (X1 ◇ ((sK2 ◇ sK2) ◇ X2)) := by
    intro sK2 X0 X2 X1
    conv => enter [1, 1]; rw [l8 sK2 X0 X1]
    conv => enter [1]; rw [l0 (sK2 ◇ sK2) X1 X2]
  have l11 : ∀ X1 sK2 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ X2)) = (sK2 ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ X2)) := by
    intro X1 sK2 X2 X0
    conv => enter [1]; rw [← l10 sK2 X0 X2 X1]
    conv => enter [1]; rw [← h4512 sK2 (X0 ◇ (sK2 ◇ sK2)) X2]
  have l12 : ∀ X1 sK2 X2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ X2)) = (sK2 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X2))) := by
    intro X1 sK2 X2 X0
    conv => enter [1]; rw [l11 X1 sK2 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ sK2) X2]
  have l13 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l8 sK2 sK0 X1]
    conv => enter [1]; rw [l12 X1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [← l8 sK2 sK0 X1]
  have l14 : ∀ sK2 X0 sK0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK0 X1
    conv => enter [1]; rw [l5 sK2 X0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l13 X1 sK2 sK0 X0]
  have l15 : ∀ sK2 X1 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [← l9 sK2 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l14 sK2 sK2 sK0 X1]
  have l16 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l8 sK2 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l15 sK2 X1 sK0]
  have l17 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l8 sK2 sK0 X0]
  have l18 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l8 sK2 sK0 X0]
  have l19 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l1 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l8 sK2 sK0 (X0 ◇ X1)]
  have l20 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l17 sK0 sK2 X0]
    conv => enter [1]; rw [← l16 sK2 sK0 sK0]
  have l21 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l18 X0 sK2 X0]
    conv => enter [1]; rw [← l18 X1 sK2 X0]
  have l22 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [← l20 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1 (sK0 ◇ (sK2 ◇ sK2))]
  have l23 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l21 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l24 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l23 sK0 sK2 X0 sK0]
  have l25 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h53861 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l19 X0 X0 sK2 sK0]
  have l26 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l25 X0 X1 sK2 sK0]
    conv => enter [1]; rw [← l22 sK2 sK0 X0 sK2]
  have l27 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l26 X0 X1 sK2 sK0]
    conv => enter [1]; rw [← l24 sK0 sK2 sK2]
  intro x y z
  conv => enter [1]; rw [← l27 x (x ◇ z) x y]

theorem Equation43_4512_53860_implies_Equation53807 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53860 : Equation53860 G) : Equation53807 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l0 sK0 sK0 X0]
    conv => enter [1]; rw [h53860 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK0 X0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  intro x
  conv => enter [1]; rw [l3 x x]

theorem Equation43_4512_54639_implies_Equation4271 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54639 : Equation54639 G) : Equation4271 G := by
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
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l5 : ∀ X0 X1 X2 X4 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X4 X5 X6
    conv => enter [1]; rw [h54639 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54639 X4 X5 X6 X0]
  have l6 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0 X3 sK0]
    conv => enter [1]; rw [← l0 X3 sK0 sK0]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l6 sK0 X1 sK0 X0 sK0]
    conv => enter [1]; rw [← l0 X1 sK0 sK0]
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

theorem Equation43_4512_54639_implies_Equation54340 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54639 : Equation54639 G) : Equation54340 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
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
    conv => enter [1]; rw [l0 (sK1 ◇ (sK2 ◇ sK3)) sK0 X0]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 X0 sK2 sK3 : G, (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 X0 sK2 sK3
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK3) X0]
  have l5 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← l0 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l6 : ∀ X0 X1 X2 X4 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X4 X5 X6
    conv => enter [1]; rw [h54639 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54639 X4 X5 X6 X0]
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

theorem Equation43_4512_54639_implies_Equation54345 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54639 : Equation54639 G) : Equation54345 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l5 : ∀ sK2 X0 sK3 sK4 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK2 X0 sK3 sK4
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ sK4)]
    conv => enter [1]; rw [l1 sK2 (sK3 ◇ sK4) X0]
  have l6 : ∀ X0 sK3 sK4 : G, (X0 ◇ (sK3 ◇ sK4)) = (sK3 ◇ (X0 ◇ sK4)) := by
    intro X0 sK3 sK4
    conv => enter [1]; rw [← l1 sK3 sK4 X0]
    conv => enter [1, 2]; rw [h43 sK4 X0]
  have l7 : ∀ X0 X1 X2 X4 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X4 X5 X6
    conv => enter [1]; rw [h54639 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54639 X4 X5 X6 X0]
  have l8 : ∀ X0 X1 X2 sK1 sK0 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK1 ◇ sK0) ◇ X3) := by
    intro X0 X1 X2 sK1 sK0 X3
    conv => enter [1]; rw [l7 X0 X1 X2 sK0 X3 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0 X3]
  have l9 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ X0) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l8 sK0 X1 sK1 sK1 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X1 sK1]
  have l10 : ∀ sK1 sK0 X0 X1 sK2 sK3 sK4 : G, ((sK1 ◇ sK0) ◇ X0) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK1 sK0 X0 X1 sK2 sK3 sK4
    conv => enter [1]; rw [← l8 sK2 X1 (sK3 ◇ sK4) sK1 sK0 X0]
    conv => enter [1]; rw [l5 sK2 X1 sK3 sK4]
  have l11 : ∀ sK1 sK0 X0 X1 sK3 sK4 : G, ((sK1 ◇ sK0) ◇ X0) = (X1 ◇ (sK3 ◇ sK4)) := by
    intro sK1 sK0 X0 X1 sK3 sK4
    conv => enter [1]; rw [← l8 sK3 X1 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [l6 sK3 X1 sK4]
  have l12 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← l9 sK1 sK0 X1 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ sK0) X1]
  have l13 : ∀ sK3 sK1 sK0 X0 sK2 sK4 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK3 sK1 sK0 X0 sK2 sK4
    conv => enter [1]; rw [l12 sK3 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l10 sK1 sK0 (sK1 ◇ sK0) X0 sK2 sK3 sK4]
  have l14 : ∀ sK3 sK1 sK0 X0 sK4 : G, (sK3 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK3 ◇ sK4)) := by
    intro sK3 sK1 sK0 X0 sK4
    conv => enter [1]; rw [l12 sK3 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l11 sK1 sK0 (sK1 ◇ sK0) X0 sK3 sK4]
  have l15 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l13 sK3 sK1 sK0 sK2 sK2 sK3]
    conv => enter [1, 2]; rw [← l14 sK3 sK1 sK0 sK2 sK3]
  have l16 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK4)) = (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l14 sK3 sK1 sK0 sK2 sK4]
    conv => enter [1]; rw [l15 sK3 sK1 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [l16 x y z w u]

theorem Equation43_4512_54639_implies_Equation54388 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54639 : Equation54639 G) : Equation54388 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK4 sK5 : G, (X0 ◇ (sK4 ◇ sK5)) = (sK4 ◇ (X0 ◇ sK5)) := by
    intro X0 sK4 sK5
    conv => enter [1]; rw [← l0 sK4 sK5 X0]
    conv => enter [1, 2]; rw [h43 sK5 X0]
  have l4 : ∀ X0 X1 X2 X4 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X4 X5 X6
    conv => enter [1]; rw [h54639 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54639 X4 X5 X6 X0]
  have l5 : ∀ X0 X1 X2 sK0 sK1 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK1) ◇ X3) := by
    intro X0 X1 X2 sK0 sK1 X3
    conv => enter [1]; rw [l4 X0 X1 X2 sK0 X3 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X3]
  have l6 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ X0) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l5 sK0 X1 sK1 sK0 sK1 X0]
    conv => enter [1]; rw [l2 sK0 X1 sK1]
  have l7 : ∀ sK0 sK1 X0 X1 sK4 sK5 : G, ((sK0 ◇ sK1) ◇ X0) = (X1 ◇ (sK4 ◇ sK5)) := by
    intro sK0 sK1 X0 X1 sK4 sK5
    conv => enter [1]; rw [← l5 sK4 X1 sK5 sK0 sK1 X0]
    conv => enter [1]; rw [l3 sK4 X1 sK5]
  have l8 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h43 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
  have l9 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l10 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l9 sK2 sK0 sK1 X0 sK2]
  have l11 : ∀ sK2 sK0 sK1 X0 sK4 sK5 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK4 ◇ sK5)) := by
    intro sK2 sK0 sK1 X0 sK4 sK5
    conv => enter [1]; rw [l10 sK2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l7 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) X0 sK4 sK5]
  intro x y z w u v
  conv => enter [1]; rw [l11 x y z w u v]
  conv => enter [1]; rw [l10 w u v x]

theorem Equation43_4512_54639_implies_Equation54683 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54639 : Equation54639 G) : Equation54683 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK2 X0]
    conv => enter [1, 1]; rw [h43 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [h43 (sK2 ◇ sK0) sK1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l4 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l1 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l5 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ X0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK2]
  have l6 : ∀ sK1 sK2 sK0 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [l2 (sK1 ◇ (sK2 ◇ sK0)) sK3 X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 sK2]
    conv => enter [1]; rw [l5 sK0 sK2 X0]
  have l8 : ∀ sK5 X0 sK6 : G, (sK5 ◇ (X0 ◇ sK6)) = (X0 ◇ (sK5 ◇ sK6)) := by
    intro sK5 X0 sK6
    conv => enter [1, 2]; rw [h43 X0 sK6]
    conv => enter [1]; rw [l2 sK5 sK6 X0]
  have l9 : ∀ sK1 sK2 sK0 X0 sK3 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK3 X0]
  have l10 : ∀ X0 X1 X2 X4 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X4 X5 X6
    conv => enter [1]; rw [h54639 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54639 X4 X5 X6 X0]
  have l11 : ∀ X0 X1 X2 sK2 sK0 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK2 ◇ sK0) ◇ X3) := by
    intro X0 X1 X2 sK2 sK0 X3
    conv => enter [1]; rw [l10 X0 X1 X2 sK0 X3 sK2]
    conv => enter [1]; rw [← l3 sK2 sK0 X3]
  have l12 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ sK0) ◇ X0) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [← l11 sK0 X1 sK2 sK2 sK0 X0]
    conv => enter [1]; rw [l7 sK0 X1 sK2]
  have l13 : ∀ sK2 sK0 X0 X1 sK5 sK6 : G, ((sK2 ◇ sK0) ◇ X0) = (X1 ◇ (sK5 ◇ sK6)) := by
    intro sK2 sK0 X0 X1 sK5 sK6
    conv => enter [1]; rw [← l11 sK5 X1 sK6 sK2 sK0 X0]
    conv => enter [1]; rw [l8 sK5 X1 sK6]
  have l14 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h43 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l12 sK2 sK0 sK1 X0]
  have l15 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK0)]
  have l16 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK2 sK0 (X0 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK1 sK2 sK0 X0]
  have l17 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l16 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK0)) sK3]
  have l18 : ∀ sK1 sK2 sK0 X0 sK3 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0 sK3
    conv => enter [1]; rw [l16 sK1 sK2 sK0 (X0 ◇ sK3)]
    conv => enter [1]; rw [l9 sK1 sK2 sK0 X0 sK3]
  have l19 : ∀ sK1 sK2 sK0 X0 sK5 sK6 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK5 ◇ sK6)) := by
    intro sK1 sK2 sK0 X0 sK5 sK6
    conv => enter [1]; rw [l18 sK1 sK2 sK0 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [l13 sK2 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0 sK5 sK6]
  have l20 : ∀ sK1 sK2 sK0 sK5 sK6 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK5 ◇ sK6) ◇ X0) := by
    intro sK1 sK2 sK0 sK5 sK6 X0
    conv => enter [1]; rw [l19 sK1 sK2 sK0 X0 sK5 sK6]
    conv => enter [1]; rw [h43 X0 (sK5 ◇ sK6)]
  have l21 : ∀ sK4 sK5 sK6 sK1 sK2 sK0 : G, (sK4 ◇ (sK5 ◇ sK6)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK4 sK5 sK6 sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK4 (sK5 ◇ sK6)]
    conv => enter [1]; rw [← l20 sK1 sK2 sK0 sK5 sK6 sK4]
  intro x y z w u v r
  conv => enter [1]; rw [l21 x y z u v r]
  conv => enter [1]; rw [l17 u v r w]

theorem Equation43_4512_54639_implies_Equation54312 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54639 : Equation54639 G) : Equation54312 G := by
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
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l5 : ∀ X0 X1 X2 X4 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X4 X5 X6
    conv => enter [1]; rw [h54639 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54639 X4 X5 X6 X0]
  have l6 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ X2)) = (X3 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [l5 X0 X1 X2 sK0 X3 sK0]
    conv => enter [1]; rw [← l0 X3 sK0 sK0]
  have l7 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l6 sK0 X1 sK0 X0 sK0]
    conv => enter [1]; rw [← l0 X1 sK0 sK0]
  have l8 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [← l6 sK1 X1 sK2 X0 sK0]
    conv => enter [1]; rw [l4 sK1 X1 sK2]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l7 sK0 sK0 X0]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l12 x y z]
  conv => enter [1]; rw [l10 x]

theorem Equation43_4512_54639_implies_Equation54313 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54639 : Equation54639 G) : Equation54313 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l4 : ∀ X0 X1 X2 X4 X5 X6 : G, (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X4 X5 X6
    conv => enter [1]; rw [h54639 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54639 X4 X5 X6 X0]
  have l5 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 sK2]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
  have l6 : ∀ X0 X1 X2 sK0 sK1 X3 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK1) ◇ X3) := by
    intro X0 X1 X2 sK0 sK1 X3
    conv => enter [1]; rw [l4 X0 X1 X2 sK0 X3 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 X3]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ X0) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l6 sK0 X1 sK1 sK0 sK1 X0]
    conv => enter [1]; rw [l3 sK0 X1 sK1]
  have l8 : ∀ X0 sK0 sK1 X1 sK2 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 X1 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 (X1 ◇ sK2) X0]
    conv => enter [1]; rw [l5 sK0 sK1 X1 sK2]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
  have l10 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l9 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 sK1 X1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation43_4512_53977_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation4268 G := by
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
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l14 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = ((X0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ sK0) X1]
  have l15 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ sK0)]
  have l16 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l17 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [← l9 sK0 X1 X0]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l17 sK0 X0 X1]
  have l20 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
  have l21 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l23 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1 X0]
  have l24 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l25 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53977 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53977 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l27 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l26 sK0 X0 X1]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l25 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l29 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l27 sK0 X0 X1]
    conv => enter [1]; rw [l19 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l28 sK0 X0 X1]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0)]
  have l31 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1]; rw [l20 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 X0 X1]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l33 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l31 sK0 X0 X1]
    conv => enter [1]; rw [l21 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l34 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l32 sK0 X0 X1]
  have l35 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l33 sK0 X0 X1]
    conv => enter [1]; rw [l7 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l36 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l34 sK0 X0 X1]
  have l37 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l35 sK0 X0 X1]
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0 sK0 sK0]
    conv => enter [1]; rw [l37 sK0 sK0 sK0]
  have l39 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [l24 X1 X2 sK0 (X0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 X0]
  have l40 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l24 X0 X1 sK0 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l41 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l24 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l38 sK0]
  have l42 : ∀ sK0 sK1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ sK1) sK0 sK0]
    conv => enter [1]; rw [l40 sK0 sK0 sK0 X2]
  have l43 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l39 sK0 sK0 sK0 sK1 X0]
    conv => enter [1]; rw [l41 sK0 sK0 sK0]
  have l44 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l43 sK0 sK1 X0]
  have l45 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [l23 sK0 X0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1 sK1]
  have l47 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [l45 sK0 sK1 X0]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l49 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1 X0]
    conv => enter [1]; rw [← l44 sK0 sK1 X0]
  have l50 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l47 sK0 sK1 sK0]
    conv => enter [1]; rw [← l49 sK0 sK1 X0]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l50 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l51 x y]

@[equational_result]
theorem Equation53977_implies_Equation53864 (G : Type*) [Magma G] (h53977 : Equation53977 G) : Equation53864 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y x (y ◇ z)]

@[equational_result]
theorem Equation53977_implies_Equation53867 (G : Type*) [Magma G] (h53977 : Equation53977 G) : Equation53867 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y x (z ◇ z)]

theorem Equation43_4512_53977_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation53868 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l2 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l3 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h53977 X3 X4 X2]
    conv => enter [1, 2]; rw [l2 X2 X2 X0 X1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK2) X0 X1]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l8 : ∀ X3 X4 X2 sK1 sK3 sK0 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro X3 X4 X2 sK1 sK3 sK0
    conv => enter [1]; rw [l3 X3 X4 X2 X3 X3]
    conv => enter [1, 2]; rw [l2 X3 X3 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l9 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l2 sK1 (sK3 ◇ sK0) sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK1 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK1 sK3 sK0 X2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0 X2
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ (sK3 ◇ sK0)) sK1 sK1]
    conv => enter [1]; rw [l8 sK1 sK1 X2 sK1 sK3 sK0]
  have l13 : ∀ sK1 sK2 X2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X2
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK1 sK1 X2]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK1 sK1]
  have l14 : ∀ sK1 sK3 sK0 X2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X2
    conv => enter [1]; rw [l9 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l13 sK1 sK1 X2]
    conv => enter [1, 2]; rw [← l9 sK1 sK3 sK0 sK1]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l14 sK1 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]

@[equational_result]
theorem Equation53977_implies_Equation53874 (G : Type*) [Magma G] (h53977 : Equation53977 G) : Equation53874 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation43_4512_53977_implies_Equation53877 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation53877 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l2 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK2 sK2 X0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation43_4512_53977_implies_Equation53890 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation53890 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l1 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l2 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l3 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h53977 X3 X4 X2]
    conv => enter [1, 2]; rw [l2 X2 X2 X0 X1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l5 : ∀ sK1 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0 X1]
  have l6 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK3 (sK3 ◇ sK0)]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK3 (sK3 ◇ sK0)]
  have l8 : ∀ X3 X4 X2 sK3 sK0 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X3 X4 X2 sK3 sK0
    conv => enter [1]; rw [l3 X3 X4 X2 X3 X3]
    conv => enter [1, 2]; rw [l2 X3 X3 sK3 (sK3 ◇ sK0)]
  have l9 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l2 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l2 sK3 sK3 sK1 (sK3 ◇ (sK3 ◇ sK0))]
  have l10 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l6 sK1 sK3 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK3 sK0 X2 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X2 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 X2
    conv => enter [1]; rw [l2 sK3 (sK3 ◇ sK0) sK3 sK3]
    conv => enter [1]; rw [l8 sK3 sK3 X2 sK3 sK0]
  have l13 : ∀ sK1 sK3 sK0 X2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0 X2
    conv => enter [1]; rw [l10 sK1 sK3 sK0]
    conv => enter [1]; rw [l12 sK3 sK0 X2]
    conv => enter [1, 2]; rw [← l10 sK1 sK3 sK0]
  have l14 : ∀ sK3 sK0 X2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X2
    conv => enter [1]; rw [l9 sK3 sK0 sK3]
    conv => enter [1]; rw [l13 sK3 sK3 sK0 X2]
    conv => enter [1, 2]; rw [← l9 sK3 sK0 sK3]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l14 sK3 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]
  conv => enter [1]; rw [l14 z w x]

theorem Equation43_4512_53977_implies_Equation53914 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation53914 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 (sK2 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [l0 sK2 sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]
  conv => enter [1]; rw [← l3 y z y]

theorem Equation43_4512_53977_implies_Equation53915 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation53915 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l2 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 (sK3 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h43 sK1 sK2]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation43_4512_53977_implies_Equation53927 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation53927 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l1 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l2 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l3 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h53977 X3 X4 X2]
    conv => enter [1, 2]; rw [l2 X2 X2 X0 X1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l5 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ sK2) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [l2 sK2 (sK3 ◇ (sK3 ◇ sK0)) X0 X1]
  have l6 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ sK2) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK2 sK3 sK0 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 sK2 sK3 (sK3 ◇ sK0)]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK3 (sK3 ◇ sK0)]
  have l8 : ∀ X3 X4 X2 sK3 sK0 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X3 X4 X2 sK3 sK0
    conv => enter [1]; rw [l3 X3 X4 X2 X3 X3]
    conv => enter [1, 2]; rw [l2 X3 X3 sK3 (sK3 ◇ sK0)]
  have l9 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l2 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l2 sK3 sK3 sK2 (sK3 ◇ (sK3 ◇ sK0))]
  have l10 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l6 sK2 sK3 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK3 sK0 X2 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X2 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 X2
    conv => enter [1]; rw [l2 sK3 (sK3 ◇ sK0) sK3 sK3]
    conv => enter [1]; rw [l8 sK3 sK3 X2 sK3 sK0]
  have l13 : ∀ sK2 sK3 sK0 X2 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0 X2
    conv => enter [1]; rw [l10 sK2 sK3 sK0]
    conv => enter [1]; rw [l12 sK3 sK0 X2]
    conv => enter [1, 2]; rw [← l10 sK2 sK3 sK0]
  have l14 : ∀ sK3 sK0 X2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X2
    conv => enter [1]; rw [l9 sK3 sK0 sK3]
    conv => enter [1]; rw [l13 sK3 sK3 sK0 X2]
    conv => enter [1, 2]; rw [← l9 sK3 sK0 sK3]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l14 sK3 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]
  conv => enter [1]; rw [l14 z w y]

theorem Equation43_4512_53977_implies_Equation53982 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation53982 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l2 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l3 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h53977 X3 X4 X2]
    conv => enter [1, 2]; rw [l2 X2 X2 X0 X1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK2) X0 X1]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK3 (sK3 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK3 (sK3 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ X3 X4 X2 sK3 sK0 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro X3 X4 X2 sK3 sK0
    conv => enter [1]; rw [l3 X3 X4 X2 X3 X3]
    conv => enter [1, 2]; rw [l2 X3 X3 sK3 (sK3 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK3 (sK0 ◇ sK0) sK3 sK3]
    conv => enter [1]; rw [l2 sK3 sK3 sK1 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK3 sK0 X2 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X2 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK3 sK0 X2
    conv => enter [1]; rw [l2 sK3 (sK3 ◇ (sK0 ◇ sK0)) sK3 sK3]
    conv => enter [1]; rw [l8 sK3 sK3 X2 sK3 sK0]
  have l13 : ∀ sK1 sK2 X2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X2
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 sK1 X2]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK1 sK1]
  have l14 : ∀ sK3 sK0 X2 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 X2
    conv => enter [1]; rw [l9 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l13 sK3 sK3 X2]
    conv => enter [1, 2]; rw [← l9 sK3 sK0 sK3 sK3]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l14 sK3 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]

theorem Equation43_4512_53977_implies_Equation53983 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53977 : Equation53977 G) : Equation53983 G := by
  have l0 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l1 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l2 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l3 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h53977 X3 X4 X2]
    conv => enter [1, 2]; rw [l2 X2 X2 X0 X1]
  have l4 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ sK2) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l0 sK2 sK3 sK2]
    conv => enter [1]; rw [l2 sK2 sK3 X0 X1]
  have l5 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK2) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK2]
    conv => enter [1]; rw [l2 sK2 (sK2 ◇ sK3) X0 X1]
  have l6 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK2) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 sK2 sK4 (sK4 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 sK2 sK4 (sK4 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ X3 X4 X2 sK4 sK1 sK0 : G, (X3 ◇ (X3 ◇ X4)) = (X2 ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro X3 X4 X2 sK4 sK1 sK0
    conv => enter [1]; rw [l3 X3 X4 X2 X3 X3]
    conv => enter [1, 2]; rw [l2 X3 X3 sK4 (sK4 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK4 (sK1 ◇ sK0) sK4 sK4]
    conv => enter [1]; rw [l2 sK4 sK4 sK2 (sK2 ◇ sK3)]
  have l10 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l6 sK2 sK3 sK4 sK1 sK0]
  have l11 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l7 sK2 sK3 sK4 sK1 sK0]
  have l12 : ∀ sK4 sK1 sK0 X2 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X2 ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK4 sK1 sK0 X2
    conv => enter [1]; rw [l2 sK4 (sK4 ◇ (sK1 ◇ sK0)) sK4 sK4]
    conv => enter [1]; rw [l8 sK4 sK4 X2 sK4 sK1 sK0]
  have l13 : ∀ sK2 sK3 X2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 X2
    conv => enter [1]; rw [l10 sK2 sK3 sK2 sK2 sK2]
    conv => enter [1]; rw [l12 sK2 sK2 sK2 X2]
    conv => enter [1, 2]; rw [← l10 sK2 sK3 sK2 sK2 sK2]
  have l14 : ∀ sK4 sK1 sK0 X2 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (X2 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X2
    conv => enter [1]; rw [l9 sK4 sK1 sK0 sK4 sK4]
    conv => enter [1]; rw [l13 sK4 sK4 X2]
    conv => enter [1, 2]; rw [← l9 sK4 sK1 sK0 sK4 sK4]
  have l15 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l14 sK4 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l15 x y z w u]

@[equational_result]
theorem Equation53977_implies_Equation53859 (G : Type*) [Magma G] (h53977 : Equation53977 G) : Equation53859 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X3 ◇ (X3 ◇ X4)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [h53977 X0 X1 X0]
    conv => enter [1]; rw [← h53977 X3 X4 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

end CommutativeSemigroup5
