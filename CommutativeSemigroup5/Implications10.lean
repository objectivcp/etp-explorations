import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_54277_implies_Equation53927 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation53927 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l5 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l6 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l7 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l4 sK2 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK3 ◇ (sK3 ◇ sK0))]
  have l8 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X1)) = (sK3 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l5 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l9 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK0) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) sK0]
    conv => enter [1]; rw [← l5 sK3 sK0 (sK3 ◇ sK0)]
  have l10 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l11 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = ((X0 ◇ sK0) ◇ (sK3 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [l5 sK3 sK0 X0]
    conv => enter [1]; rw [l0 sK3 (X0 ◇ sK0) X1]
  have l12 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK3 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l11 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK3 X1 (X0 ◇ sK0)]
  have l13 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l14 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = ((sK3 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l12 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l8 sK3 sK0 X1 X0]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
  have l16 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l14 sK3 sK0 X0 X1]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← l1 X2 X3 (X0 ◇ X1)]
  have l19 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l1 sK2 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l20 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l6 sK3 sK0 sK3]
    conv => enter [1]; rw [← h54277 sK0 X0 sK3]
  have l21 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← h54277 sK2 X0 sK1]
  have l22 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l20 sK3 sK0 X0]
  have l23 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l21 sK1 sK2 X0]
  have l24 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l22 sK3 sK0 X0]
    conv => enter [1]; rw [← l1 X0 X0 sK0]
  have l25 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [h54277 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l22 sK3 sK0 sK0]
  have l26 : ∀ X0 X1 sK0 sK3 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro X0 X1 sK0 sK3
    conv => enter [1]; rw [h54277 (X0 ◇ X0) X1 sK0]
    conv => enter [1, 2, 2]; rw [← l22 sK3 sK0 X0]
  have l27 : ∀ X0 X1 sK3 sK0 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l26 X0 X1 sK0 sK3]
    conv => enter [1]; rw [l17 sK0 sK0 sK3 (sK3 ◇ (sK3 ◇ sK0))]
  have l28 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK0 ◇ sK3)) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [l25 sK0 X0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 (sK3 ◇ (sK3 ◇ sK0))]
  have l29 : ∀ X0 X1 sK3 sK0 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l27 X0 X1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK3 sK0 (sK0 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
  have l30 : ∀ sK3 sK0 X0 : G, (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l1 (sK3 ◇ (sK3 ◇ sK0)) sK0 sK3]
    conv => enter [1]; rw [← l28 sK0 X0 sK3]
  have l31 : ∀ X0 X1 sK3 sK0 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK0)) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l29 X0 X1 sK3 sK0]
    conv => enter [1]; rw [l16 sK3 sK0 sK0 (sK3 ◇ (sK3 ◇ sK0))]
  have l32 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l30 sK3 sK0 sK3]
    conv => enter [1]; rw [← l22 sK3 sK0 sK3]
  have l33 : ∀ X0 X1 sK3 sK0 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l31 X0 X1 sK3 sK0]
    conv => enter [1, 2]; rw [l9 sK3 sK0]
  have l34 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l5 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l32 sK3 sK0]
  have l35 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [← h54277 (sK3 ◇ sK0) (sK3 ◇ sK0) sK3]
    conv => enter [1]; rw [← l33 X0 X1 sK3 sK0]
  have l36 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l35 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ X1)]
  have l37 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l34 sK3 sK0]
  have l38 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l23 sK1 sK2 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h54277 (X1 ◇ X1) X1 X0]
  have l39 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l23 sK1 sK2 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l19 sK2 (sK3 ◇ (sK3 ◇ sK0)) sK3 sK0]
  have l40 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h54277 sK2 X0 sK2]
    conv => enter [1, 2]; rw [← l23 sK1 sK2 sK2]
  have l41 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l40 sK2 X0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l42 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l38 sK1 sK2 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l36 sK3 sK0 X0 sK1]
  have l43 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l41 sK2 X0 sK1]
  have l44 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l42 sK1 sK2 X0 sK3 sK0]
    conv => enter [1, 2, 2]; rw [← l37 sK3 sK0]
  have l45 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l43 sK1 sK2 sK1]
    conv => enter [1]; rw [← l23 sK1 sK2 sK1]
  have l46 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l44 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [← l7 sK2 sK3 sK0 X0 (sK3 ◇ (sK3 ◇ sK0))]
  have l47 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l46 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l1 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) X0 (sK3 ◇ (sK3 ◇ sK0))]
  have l48 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1, 2]; rw [l39 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
  have l49 : ∀ sK3 sK0 sK2 X0 sK1 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l39 sK1 sK2 sK3 sK0]
  have l50 : ∀ sK3 sK0 sK2 X0 sK1 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1]; rw [l1 (sK3 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [← l39 sK1 sK2 sK3 sK0]
  have l51 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l47 sK1 sK2 sK1 sK1 X0]
    conv => enter [1]; rw [l50 sK1 sK1 sK2 X0 sK1]
  have l52 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l49 sK3 sK0 sK2 X0 sK1]
  have l53 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [l48 sK2 sK1 sK3 sK0]
  have l54 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l47 sK1 sK2 sK1 sK1 X0]
    conv => enter [1]; rw [← l52 sK1 sK2 X0 sK1 sK1]
  have l55 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l53 sK1 sK2 sK3 sK0]
  have l56 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l45 sK1 sK2]
    conv => enter [1]; rw [l55 sK1 sK2 sK3 sK0]
  have l57 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK3 sK0 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l56 sK1 sK2 sK3 sK0]
  have l58 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l59 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l58 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ sK2)) sK0 sK1]
  have l60 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l54 sK1 sK2 sK0]
    conv => enter [1]; rw [← l59 sK3 sK0 sK1 sK2]
  have l61 : ∀ sK3 sK0 X0 sK1 sK2 : G, (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 X0 sK1 sK2
    conv => enter [1]; rw [l1 sK3 (sK3 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [l60 sK3 sK0 sK1 sK2]
  have l62 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l51 sK1 sK2 X0]
    conv => enter [1]; rw [← l61 sK3 sK0 X0 sK1 sK2]
  have l63 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l24 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l64 : ∀ sK3 sK0 X1 X0 : G, ((sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X1) = ((X0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X1 X0
    conv => enter [1, 1]; rw [l24 sK3 sK0 X0]
    conv => enter [1]; rw [l0 X0 (X0 ◇ sK0) X1]
  have l65 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l24 sK3 sK0 sK3]
    conv => enter [1]; rw [l60 sK3 sK0 sK1 sK2]
  have l66 : ∀ sK3 sK0 X1 X0 : G, ((sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK3 sK0 X1 X0
    conv => enter [1]; rw [l64 sK3 sK0 X1 X0]
    conv => enter [1]; rw [← l1 X0 X1 (X0 ◇ sK0)]
  have l67 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ ((X1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l63 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ sK0) (X0 ◇ X1)]
  have l68 : ∀ sK3 sK0 X1 X0 : G, (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK3 sK0 X1 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ (sK3 ◇ sK0)) X1]
    conv => enter [1]; rw [l66 sK3 sK0 X1 X0]
  have l69 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l67 sK3 sK0 X0 X1]
    conv => enter [1]; rw [l18 X0 (X1 ◇ sK0) X0 X1]
  have l70 : ∀ sK1 sK2 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l62 sK1 sK2 sK1 sK0 X1]
    conv => enter [1]; rw [l68 sK1 sK0 X1 X0]
  have l71 : ∀ sK1 sK2 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l60 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l69 sK1 sK0 X0 X1]
  have l72 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l65 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l70 sK3 sK3 X0 X1 sK0]
  have l73 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ sK0)))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l65 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l71 sK3 sK3 X0 X1 sK0]
  have l74 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l73 sK3 sK0 X0 sK3]
    conv => enter [1, 2]; rw [← l72 sK3 sK0 sK3 X0]
  have l75 : ∀ sK3 sK0 X0 sK1 sK2 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK3 sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l65 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l76 : ∀ sK3 sK0 X0 sK1 sK2 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 X0 sK1 sK2
    conv => enter [1]; rw [l75 sK3 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← l54 sK1 sK2 X0]
  have l77 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l65 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [← l76 sK3 sK0 X0 sK3 sK3]
  have l78 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l77 sK3 sK0 ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0))]
    conv => enter [1]; rw [← h54277 X0 X1 (sK3 ◇ (sK3 ◇ sK0))]
  have l79 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l1 X0 X0 X1]
    conv => enter [1]; rw [← l78 sK3 sK0 X1 X0]
  intro x y z w
  conv => enter [1]; rw [l79 x y z w]
  conv => enter [1]; rw [l74 z w y]

theorem Equation43_4512_54277_implies_Equation53982 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation53982 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK3 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l7 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
  have l10 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK2) X0]
  have l11 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 X0 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK3 (sK0 ◇ sK0) X0]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l6 X2 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54277 X0 X1 sK0]
  have l14 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54277 X0 X1 X0]
    conv => enter [1]; rw [← h54277 X0 X3 X0]
  have l15 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ sK3) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK3]
    conv => enter [1]; rw [← h54277 (sK0 ◇ sK0) X0 sK3]
  have l16 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← h54277 sK2 X0 sK1]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54277 sK0 X0 sK0]
  have l18 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ sK3) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l15 sK3 sK0 sK3]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ sK0) sK3]
  have l19 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l16 sK1 sK2 sK1]
    conv => enter [1]; rw [← l13 sK0 sK2 sK1]
  have l20 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ sK3) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l18 sK3 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l19 sK1 sK2 sK0]
  have l22 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ sK3) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l20 sK3 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
  have l23 : ∀ sK0 sK3 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ sK3) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l22 sK3 sK0]
  have l24 : ∀ sK0 sK3 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l23 sK0 sK3]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) sK3]
  have l25 : ∀ sK0 X0 sK3 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [h54277 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l24 sK0 sK3]
  have l26 : ∀ sK0 X0 sK3 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l24 sK0 sK3]
  have l27 : ∀ sK0 X0 sK3 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [l26 sK0 X0 sK3]
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) X0]
  have l28 : ∀ sK0 X0 sK3 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (sK3 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [l25 sK0 X0 sK3]
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) (sK0 ◇ sK0) sK3 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
  have l29 : ∀ sK0 X0 sK3 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [l28 sK0 X0 sK3]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))]
  have l30 : ∀ sK0 X0 sK3 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [l29 sK0 X0 sK3]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) (sK3 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 X0 sK3 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [l30 sK0 X0 sK3]
    conv => enter [1]; rw [l12 (sK0 ◇ sK0) (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) (sK3 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK0 sK3 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l31 sK0 sK0 sK3]
  have l33 : ∀ sK0 sK3 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l13 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l32 sK0 sK3]
  have l34 : ∀ sK0 sK3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l33 sK0 sK3]
  have l35 : ∀ sK0 sK3 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l34 sK0 sK3]
  have l36 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l24 sK0 sK3]
    conv => enter [1]; rw [l35 sK0 sK3]
  have l37 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 sK0]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l1 X0 X0 sK0]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [l1 sK0 X0 X0]
  have l40 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← h54277 (X0 ◇ X0) X1 sK0]
  have l41 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l17 sK0 X1]
  have l42 : ∀ sK0 X0 X1 sK3 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 sK3
    conv => enter [1]; rw [l41 sK0 X0 X1]
    conv => enter [1, 2]; rw [l24 sK0 sK3]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l40 sK0 X0 sK0]
    conv => enter [1]; rw [← l13 sK0 (X0 ◇ X0) sK0]
  have l44 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l24 sK0 sK3]
    conv => enter [1]; rw [l39 sK0 X0]
  have l45 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l24 sK0 sK3]
    conv => enter [1]; rw [l38 sK0 X0]
  have l46 : ∀ sK0 sK3 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [l24 sK0 sK3]
  have l47 : ∀ sK0 sK3 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l43 sK0 sK0]
    conv => enter [1]; rw [l42 sK0 (sK0 ◇ sK0) sK0 sK3]
  have l48 : ∀ sK0 sK3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l46 sK0 sK3]
  have l49 : ∀ sK0 sK3 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l47 sK0 sK3]
    conv => enter [1]; rw [← l1 sK3 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l50 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l12 sK3 (sK0 ◇ sK0) (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l49 sK0 sK3]
  have l51 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l50 sK3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l52 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l51 sK3 sK0]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l53 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l52 sK3 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0 (sK0 ◇ sK0)]
  have l54 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l53 sK3 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
  have l55 : ∀ sK0 sK3 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK3 ◇ ((sK0 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l54 sK3 sK0]
  have l56 : ∀ sK0 sK3 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l55 sK0 sK3]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK0) (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
  have l57 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l56 sK0 sK3]
    conv => enter [1]; rw [l24 sK0 sK3]
  have l58 : ∀ sK0 sK3 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l48 sK0 sK3]
    conv => enter [1]; rw [← l57 sK3 sK0]
  have l59 : ∀ sK3 sK0 X0 : G, (sK3 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l48 sK0 sK3]
  have l60 : ∀ sK0 X0 sK3 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l59 sK3 sK0 X0]
  have l61 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l21 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK2)]
  have l62 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ sK2)) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l61 sK0 sK1 sK2]
    conv => enter [1]; rw [l27 sK0 sK2 sK3]
  have l63 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l60 sK0 sK2 sK0]
    conv => enter [1]; rw [← l62 sK0 sK1 sK2 sK0]
  have l64 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK0]
    conv => enter [1]; rw [l63 sK0 sK2 sK1]
  have l65 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l44 sK3 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0 X0]
  have l66 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 sK0]
    conv => enter [1]; rw [l65 sK0 sK0 X0]
  have l67 : ∀ sK0 X1 X0 sK3 : G, (sK0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X0 sK3
    conv => enter [1]; rw [h54277 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l45 sK3 sK0 X0]
  have l68 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l48 sK0 X0]
    conv => enter [1]; rw [← l67 sK0 X1 X0 X0]
  have l69 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [← l68 X0 sK0 sK0]
  have l70 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l24 sK0 sK3]
    conv => enter [1]; rw [l69 sK0 X0]
  have l71 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 sK0]
    conv => enter [1]; rw [l70 sK0 sK0 X0]
  have l72 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) ◇ X0) = (((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1, 1]; rw [l36 sK3 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) X0]
  have l73 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK3 sK0
    conv => enter [1, 2]; rw [l36 sK3 sK0]
    conv => enter [1]; rw [l6 X0 (sK0 ◇ sK0) ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))]
  have l74 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l73 X0 sK3 sK0]
    conv => enter [1, 2, 2]; rw [← l58 sK0 sK3]
  have l75 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l72 sK3 sK0 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X0 ((sK3 ◇ (sK0 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))]
  have l76 : ∀ sK0 X0 sK3 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l74 X0 sK3 sK0]
  have l77 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l75 sK3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l58 sK0 sK3]
  have l78 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l48 sK0 X0]
    conv => enter [1]; rw [← l76 sK0 X0 X0]
  have l79 : ∀ sK0 X0 sK3 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l77 sK3 sK0 X0]
  have l80 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l71 sK0 X0]
    conv => enter [1]; rw [l78 X0 sK0]
  have l81 : ∀ sK3 sK0 X0 : G, (sK3 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [← l79 sK0 X0 sK3]
  have l82 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l80 sK0 X0]
    conv => enter [1]; rw [← l81 sK3 sK0 X0]
  have l83 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l64 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l84 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l83 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l85 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l84 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0) sK1]
  have l86 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l64 sK1 sK2 sK0]
    conv => enter [1]; rw [l85 sK0 sK1 sK2]
  have l87 : ∀ X0 sK0 X1 : G, ((X0 ◇ X0) ◇ (sK0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l0 sK0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l66 sK0 X0]
  have l88 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l66 sK0 X1]
    conv => enter [1]; rw [l6 X0 sK0 (X1 ◇ X1)]
  have l89 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l71 sK0 X0]
    conv => enter [1]; rw [l88 X0 sK0 X1]
  have l90 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ X0) ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l87 X0 sK0 X1]
  have l91 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (sK0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l90 sK0 X1 X0]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ X0)]
  have l92 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l89 sK0 X1 sK0]
    conv => enter [1]; rw [← l91 sK0 X1 sK0]
  have l93 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l71 sK0 X0]
    conv => enter [1]; rw [l6 X0 sK0 (sK0 ◇ sK0)]
  have l94 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l92 sK0 sK2]
    conv => enter [1]; rw [← l21 sK1 sK2 sK0]
  have l95 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l10 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [l14 sK1 (sK1 ◇ sK2) X0]
  have l96 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l95 sK1 sK2 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1 sK1]
  have l97 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l96 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0) sK1]
  have l98 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l93 sK0 sK1]
    conv => enter [1]; rw [← l97 sK1 sK2 sK0]
  have l99 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l10 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [l14 sK1 (sK1 ◇ sK2) sK0]
  have l100 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l14 sK3 sK0 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l82 sK0 sK3 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
  have l101 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 (sK1 ◇ (sK1 ◇ sK2)) sK0 X0]
  have l102 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l101 sK1 sK2 sK0 sK0]
  have l103 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l98 sK0 sK1 sK0]
    conv => enter [1]; rw [l99 sK1 sK0 sK0]
  have l104 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l102 sK0 sK1 sK2]
  have l105 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l100 sK3 sK0]
    conv => enter [1]; rw [l103 sK0 sK1]
  have l106 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l104 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK2))]
  have l107 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l93 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l106 sK1 sK2 sK0]
  have l108 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l100 sK3 sK0]
    conv => enter [1]; rw [l107 sK0 sK1 sK2]
  have l109 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l86 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l108 sK3 sK0 sK1 sK2]
  have l110 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l94 sK0 sK1 sK0]
    conv => enter [1]; rw [l109 sK1 sK0 sK3 sK0]
  have l111 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l100 sK3 sK0]
    conv => enter [1]; rw [l110 sK0 sK1 sK3]
  have l112 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l105 sK3 sK0 sK1]
    conv => enter [1]; rw [l11 sK3 sK1 sK0]
  have l113 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l111 sK3 sK0 sK3]
  have l114 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1, 1]; rw [l100 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l115 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l114 sK3 sK0 X0]
    conv => enter [1]; rw [← l92 sK0 X0]
  have l116 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK0 ◇ sK0)) = ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l100 sK3 sK0]
    conv => enter [1]; rw [← l115 sK3 sK0 X0]
  have l117 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l116 sK3 sK0 ((sK3 ◇ (sK0 ◇ sK0)) ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0))]
    conv => enter [1]; rw [← h54277 X0 X1 (sK3 ◇ (sK0 ◇ sK0))]
  have l118 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l1 X0 X0 X1]
    conv => enter [1]; rw [l117 X1 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l118 x y z w]
  conv => enter [1]; rw [l113 z w]

theorem Equation43_4512_54277_implies_Equation53983 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation53983 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l3 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK4 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK4 (sK4 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l5 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK3) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) sK3]
    conv => enter [1]; rw [← l2 sK2 sK3 (sK2 ◇ sK3)]
  have l6 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l3 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK2 ◇ sK3)]
  have l7 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l9 X0 X1 X2 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l8 X2 X0 X1]
  have l14 : ∀ sK2 sK3 X0 X1 : G, (((sK2 ◇ sK3) ◇ X0) ◇ (X1 ◇ X1)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h54277 ((sK2 ◇ sK3) ◇ X0) X1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 (sK2 ◇ sK3) X0]
  have l15 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [h54277 sK3 X0 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2, 2]; rw [l5 sK2 sK3]
  have l16 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK4) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [← h54277 (sK1 ◇ sK0) X0 sK4]
  have l17 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK2) = (sK3 ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l3 sK2 sK3 sK2]
    conv => enter [1]; rw [← h54277 sK3 X0 sK2]
  have l18 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [l15 sK3 X0 sK2]
    conv => enter [1]; rw [l11 (sK2 ◇ (sK2 ◇ sK3)) (sK2 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK3) (sK2 ◇ sK3)]
  have l19 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0))) = ((sK2 ◇ sK3) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [← l14 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) X0 (X1 ◇ X1)]
  have l20 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [h43 sK4 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l16 sK4 sK1 sK0 X0]
  have l21 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l17 sK2 sK3 X0]
  have l22 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [l18 sK3 X0 sK2]
    conv => enter [1]; rw [l12 (sK2 ◇ sK3) (sK2 ◇ (sK2 ◇ sK3)) (sK2 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK3)]
  have l23 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [l22 sK3 X0 sK2]
    conv => enter [1]; rw [l11 (sK2 ◇ sK3) (sK2 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK3) (sK2 ◇ (sK2 ◇ sK3))]
  have l24 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [l23 sK3 X0 sK2]
    conv => enter [1]; rw [← l19 sK2 sK3 (sK2 ◇ sK3) (sK2 ◇ (sK2 ◇ sK3))]
  have l25 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [l24 sK3 X0 sK2]
    conv => enter [1]; rw [← l6 sK2 sK3 sK2 (sK2 ◇ (sK2 ◇ sK3))]
  have l26 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [l25 sK3 X0 sK2]
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ (sK2 ◇ sK3)) (sK2 ◇ (sK2 ◇ sK3))]
  have l27 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l21 sK2 sK3 sK2]
    conv => enter [1]; rw [l26 sK3 sK2 sK2]
  have l28 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l20 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← l1 X0 X0 (sK1 ◇ sK0)]
  have l29 : ∀ sK1 sK0 X0 sK4 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 sK4
    conv => enter [1]; rw [h54277 (sK1 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l20 sK4 sK1 sK0 (sK1 ◇ sK0)]
  have l30 : ∀ X0 X1 sK1 sK0 sK4 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 X1 sK1 sK0 sK4
    conv => enter [1]; rw [h54277 (X0 ◇ X0) X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l20 sK4 sK1 sK0 X0]
  have l31 : ∀ X0 X1 sK4 sK1 sK0 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (sK4 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l30 X0 X1 sK1 sK0 sK4]
    conv => enter [1]; rw [l11 (sK1 ◇ sK0) (sK1 ◇ sK0) sK4 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l32 : ∀ sK1 sK0 X0 sK4 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = (sK4 ◇ ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 sK4
    conv => enter [1]; rw [l29 sK1 sK0 X0 sK4]
    conv => enter [1]; rw [← l1 sK4 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
  have l33 : ∀ sK4 sK1 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l31 X0 X1 sK4 sK1 sK0]
  have l34 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l13 sK4 (sK1 ◇ sK0) (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l32 sK1 sK0 X0 sK4]
  have l35 : ∀ sK4 sK1 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l33 sK4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ X1)]
  have l36 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l34 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [← l20 sK4 sK1 sK0 sK4]
  have l37 : ∀ X0 X1 sK1 sK0 sK4 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ sK0) ◇ ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK1 sK0 sK4
    conv => enter [1]; rw [← l35 sK4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK0) (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) (sK4 ◇ (sK1 ◇ sK0))]
  have l38 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ sK0) (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l36 sK4 sK1 sK0]
  have l39 : ∀ X0 X1 sK1 sK0 sK4 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ sK0) ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK1 sK0 sK4
    conv => enter [1]; rw [l37 X0 X1 sK1 sK0 sK4]
    conv => enter [1]; rw [l13 (sK1 ◇ sK0) (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) (sK4 ◇ (sK1 ◇ sK0))]
  have l40 : ∀ X0 X1 sK1 sK0 sK4 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK1 sK0 sK4
    conv => enter [1]; rw [l39 X0 X1 sK1 sK0 sK4]
    conv => enter [1, 2]; rw [l38 sK4 sK1 sK0]
  have l41 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (sK4 ◇ ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l40 X0 X1 sK1 sK0 sK4]
    conv => enter [1]; rw [← l1 sK4 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
  have l42 : ∀ sK4 sK1 sK0 X0 X1 : G, (sK4 ◇ ((sK1 ◇ sK0) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l13 sK4 (sK1 ◇ sK0) (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l41 X0 X1 sK4 sK1 sK0]
  have l43 : ∀ sK4 sK1 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ sK0) (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l42 sK4 sK1 sK0 X0 X1]
  have l44 : ∀ sK4 sK1 sK0 X0 X1 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [← l38 sK4 sK1 sK0]
    conv => enter [1]; rw [l43 sK4 sK1 sK0 X0 X1]
  have l45 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [h54277 sK3 X0 sK3]
    conv => enter [1, 2]; rw [← l21 sK2 sK3 sK3]
  have l46 : ∀ X0 X1 sK3 sK2 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (sK3 ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro X0 X1 sK3 sK2
    conv => enter [1]; rw [h54277 (X0 ◇ X0) X1 sK3]
    conv => enter [1, 2, 2]; rw [← l21 sK2 sK3 X0]
  have l47 : ∀ X0 X1 sK2 sK3 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l46 X0 X1 sK3 sK2]
    conv => enter [1]; rw [l11 sK3 sK3 sK2 (sK2 ◇ (sK2 ◇ sK3))]
  have l48 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK3 ◇ sK2)) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [l45 sK3 X0 sK2]
    conv => enter [1]; rw [l1 sK3 sK2 (sK2 ◇ (sK2 ◇ sK3))]
  have l49 : ∀ X0 X1 sK2 sK3 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l47 X0 X1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK2 sK3 (sK3 ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l50 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK3)) = (sK3 ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← l1 (sK2 ◇ (sK2 ◇ sK3)) sK3 sK2]
    conv => enter [1]; rw [← l48 sK3 X0 sK2]
  have l51 : ∀ X0 X1 sK2 sK3 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK3)) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l49 X0 X1 sK2 sK3]
    conv => enter [1]; rw [l13 (sK2 ◇ sK3) sK3 (sK2 ◇ (sK2 ◇ sK3))]
  have l52 : ∀ sK2 sK3 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l50 sK2 sK3 sK2]
    conv => enter [1]; rw [← l21 sK2 sK3 sK2]
  have l53 : ∀ X0 X1 sK2 sK3 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l51 X0 X1 sK2 sK3]
    conv => enter [1, 2]; rw [l5 sK2 sK3]
  have l54 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l2 sK2 sK3 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l52 sK2 sK3]
  have l55 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [← h54277 (sK2 ◇ sK3) (sK2 ◇ sK3) sK2]
    conv => enter [1]; rw [← l53 X0 X1 sK2 sK3]
  have l56 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l55 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ X1)]
  have l57 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l44 sK4 sK1 sK0 sK4 sK4]
    conv => enter [1]; rw [← l56 sK2 sK3 sK4 sK4]
  have l58 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1, 2]; rw [← l54 sK2 sK3]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK3) (sK2 ◇ (sK2 ◇ sK3))]
  have l59 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l57 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l58 sK2 sK3]
  have l60 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l27 sK2 sK3]
    conv => enter [1, 2]; rw [← l59 sK4 sK1 sK0 sK2 sK3]
  have l61 : ∀ sK2 sK3 X0 : G, (((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h54277 ((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3))) X0 sK2]
    conv => enter [1, 2, 2]; rw [← l27 sK2 sK3]
  have l62 : ∀ sK2 sK4 sK1 sK0 sK3 X0 : G, (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) = (((sK2 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X0)) := by
    intro sK2 sK4 sK1 sK0 sK3 X0
    conv => enter [1, 2]; rw [l57 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l61 sK2 sK3 X0]
  have l63 : ∀ sK2 sK4 sK1 sK0 sK3 X0 : G, (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ X0))) := by
    intro sK2 sK4 sK1 sK0 sK3 X0
    conv => enter [1]; rw [l62 sK2 sK4 sK1 sK0 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK3)) (sK2 ◇ (sK2 ◇ sK3)) (X0 ◇ X0)]
  have l64 : ∀ sK4 sK1 sK0 sK2 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK4 sK1 sK0 sK2
    conv => enter [1]; rw [l44 sK4 sK1 sK0 (sK2 ◇ (sK2 ◇ sK4)) sK4]
    conv => enter [1]; rw [← l63 sK2 sK4 sK1 sK0 sK4 sK4]
  have l65 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l60 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l64 sK4 sK1 sK0 sK2]
  have l66 : ∀ sK1 sK0 X1 X0 sK4 : G, ((sK1 ◇ sK0) ◇ (X1 ◇ X1)) = (X0 ◇ (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X1 X0 sK4
    conv => enter [1]; rw [h54277 (sK1 ◇ sK0) X1 X0]
    conv => enter [1, 2]; rw [← l28 sK4 sK1 sK0 X0]
  have l67 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [← l28 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [← l65 sK2 sK3 sK4 sK1 sK0]
  have l68 : ∀ sK1 sK0 X1 X0 sK2 sK3 : G, ((sK1 ◇ sK0) ◇ (X1 ◇ X1)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK0 X1 X0 sK2 sK3
    conv => enter [1]; rw [l66 sK1 sK0 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l65 sK2 sK3 sK1 sK1 sK0]
  have l69 : ∀ sK4 sK1 sK0 X0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK4 sK1 sK0 X0 sK2 sK3
    conv => enter [1]; rw [l20 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [l68 sK1 sK0 sK4 X0 sK2 sK3]
  have l70 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l69 sK4 sK1 sK0 X0 sK4 sK4]
    conv => enter [1, 2]; rw [← l67 sK4 sK1 sK0 sK4 sK4]
  have l71 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [h43 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [← l70 sK4 sK1 sK0 X0]
  have l72 : ∀ sK4 sK1 sK0 X0 sK2 sK3 : G, ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK4 sK1 sK0 X0 sK2 sK3
    conv => enter [1]; rw [l71 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← l65 sK2 sK3 sK4 sK1 sK0]
  have l73 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l67 sK4 sK1 sK0 sK4 sK4]
    conv => enter [1]; rw [← l72 sK4 sK1 sK0 X0 sK4 sK4]
  have l74 : ∀ sK4 sK1 sK0 X0 X1 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l73 sK4 sK1 sK0 ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0))]
    conv => enter [1]; rw [← h54277 X0 X1 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l75 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l1 X0 X0 X1]
    conv => enter [1]; rw [← l74 sK4 sK1 sK0 X1 X0]
  intro x y z w u
  conv => enter [1]; rw [l75 x y z w u]

theorem Equation43_4512_54277_implies_Equation53859 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation53859 G := by
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
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l15 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK0 ◇ sK1)]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK1)]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l23 sK0 sK1 X0]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [l22 sK0 sK1]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l18 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l30 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l31 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l32 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 X1]
    conv => enter [1]; rw [l31 sK0 X0 X1]
  have l33 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l34 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l33 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l35 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l34 X0 X1 X2 X3]
  have l36 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l35 X0 X1 X2 X3]
  have l37 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54277 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l26 sK0 sK1]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54277 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54277 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l14 sK0]
  have l40 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54277 X0 X1 sK0]
  have l41 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h54277 X0 X1 (sK0 ◇ sK0)]
  have l42 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 (sK1 ◇ (sK1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54277 X0 X1 sK1]
  have l43 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← l42 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l28 sK0 sK1 (sK1 ◇ X0)]
  have l44 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l40 sK0 X0 X1]
  have l45 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 X0]
    conv => enter [1]; rw [l36 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l46 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l47 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l37 sK0 X0 sK1]
    conv => enter [1]; rw [l36 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54277 sK1 sK0 sK0]
    conv => enter [1]; rw [← l41 sK0 sK1 sK0]
  have l49 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1]; rw [l10 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l50 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l46 sK0 sK0]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l47 sK0 sK0 sK1]
    conv => enter [1]; rw [← l41 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l53 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1]; rw [← l32 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l54 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l50 sK0]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l52 sK0 sK1]
  have l57 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l53 sK0 X0]
    conv => enter [1]; rw [← l41 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l58 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l54 sK0]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l55 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l56 sK0 sK1]
  have l61 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l57 sK0 X0]
    conv => enter [1]; rw [← l41 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l59 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l64 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l61 sK0 X0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l65 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l64 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l63 sK0 sK1]
  have l67 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l58 sK0]
    conv => enter [1]; rw [← l65 sK0 X0]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l36 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l69 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l67 sK0 sK0]
    conv => enter [1]; rw [← l41 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l71 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l69 sK0]
    conv => enter [1]; rw [← l29 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← l44 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l73 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l71 sK0]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK1))]
  have l75 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l73 sK0]
  have l76 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l75 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l77 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l76 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l78 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK1))]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [← l79 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0]
    conv => enter [1]; rw [← l80 sK0 sK1]
  have l82 : ∀ X1 X2 X0 sK0 : G, ((X1 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54277 (X1 ◇ X1) X2 X0]
    conv => enter [1, 2, 2]; rw [← l44 sK0 X0 X1]
  have l83 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l44 sK0 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l84 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l44 sK0 sK0 sK0]
  have l85 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l84 sK0]
  have l86 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l83 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l87 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l82 X1 X0 X0 sK0]
    conv => enter [1]; rw [← l41 sK0 (X1 ◇ X1) X0]
  have l88 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l85 sK0]
  have l89 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l43 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 sK1]
    conv => enter [1]; rw [← l87 X0 sK0 sK0]
  have l90 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l86 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X0]
    conv => enter [1]; rw [← l89 sK0 sK1 X0]
  have l91 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l90 sK0 X0 sK1]
    conv => enter [1]; rw [← l86 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) (sK0 ◇ sK1)]
  have l92 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l91 sK0 X0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l93 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l92 sK0 X0 sK1]
    conv => enter [1]; rw [← l77 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l94 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l93 sK0 X0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK1))]
  have l95 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [← l94 sK0 X0 sK1]
  have l96 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l86 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l95 sK0 sK1 X0]
  have l97 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l96 sK0 X0 sK0]
  have l98 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l88 sK0]
    conv => enter [1]; rw [l97 sK0 X0]
  have l99 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l44 sK0 X0 sK0]
  have l100 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l98 sK0 X0]
    conv => enter [1]; rw [← l99 sK0 X0]
  have l101 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l100 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l101 x y]
  conv => enter [1]; rw [l88 x]

theorem Equation43_4512_54277_implies_Equation54161 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation54161 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54277 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h43 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l1 X0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l2 x x y]

theorem Equation43_4512_54277_implies_Equation53977 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation53977 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54277 X0 X1 sK0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h54277 X0 X1 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h54277 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l10 sK0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [l0 X0 X1 X1]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54277 X0 X1 X0]
    conv => enter [1, 2]; rw [← l8 sK0 X0 X0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0 sK0 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0 sK0]
    conv => enter [1]; rw [l15 X0 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [l3 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l19 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l21 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
    conv => enter [1]; rw [← h54277 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X0 X1]
    conv => enter [1]; rw [← l22 sK0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l23 x y z]
  conv => enter [1]; rw [l16 z]

theorem Equation43_4512_54277_implies_Equation53861 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation53861 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← h54277 sK1 X0 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 X0 X0 sK1]
  have l5 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (X1 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1, 2]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h54277 sK1 X1 X0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [← l5 X0 sK0 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l4 sK0 sK1 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1, 1]; rw [l4 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))]
    conv => enter [1]; rw [← h54277 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l0 X0 X0 X1]
    conv => enter [1]; rw [← l9 sK0 sK1 X1 X0]
  intro x y z
  conv => enter [1]; rw [l10 x y x z]
  conv => enter [1]; rw [← l4 x z x]

theorem Equation43_4512_54277_implies_Equation54163 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation54163 G := by
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
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l6 X0 X1 X2 X3]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l10 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54277 sK1 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l4 sK0 sK1]
  have l11 : ∀ X2 X0 X3 X1 : G, ((X2 ◇ X0) ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h54277 (X2 ◇ X0) X3 X2]
    conv => enter [1, 2]; rw [← h54277 X0 X1 X2]
  have l12 : ∀ sK2 X0 X1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [← h54277 X0 X1 sK2]
  have l13 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54277 X0 X1 X0]
    conv => enter [1]; rw [← h54277 X0 X3 X0]
  have l14 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54277 sK2 X0 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54277 sK1 sK0 sK0]
    conv => enter [1]; rw [← l12 sK2 sK1 sK0]
  have l16 : ∀ X2 X0 X1 sK2 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X2 ◇ X0))) := by
    intro X2 X0 X1 sK2
    conv => enter [1]; rw [← l11 X2 X0 X2 X1]
    conv => enter [1]; rw [← l12 sK2 (X2 ◇ X0) X2]
  have l17 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l10 sK1 X0 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
  have l19 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l17 sK1 X0 sK0]
    conv => enter [1]; rw [l9 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
  have l21 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l19 sK1 X0 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l22 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l21 sK1 X0 sK0]
    conv => enter [1]; rw [l16 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) sK2]
  have l23 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l22 sK1 X0 sK2 sK1]
    conv => enter [1]; rw [l16 sK2 (sK2 ◇ sK2) (sK1 ◇ sK1) sK2]
  have l24 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l23 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l8 (sK2 ◇ sK2) sK2 sK2 sK2]
  have l25 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l24 sK1 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l26 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l25 sK1 X0 sK2]
    conv => enter [1]; rw [← l12 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l27 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l26 sK1 X0 sK2]
    conv => enter [1]; rw [← l12 sK2 sK2 (sK2 ◇ sK2)]
  have l28 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l27 sK1 X0 sK2]
    conv => enter [1]; rw [l1 sK2 (sK2 ◇ sK2) sK2]
  have l29 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l28 sK1 X0 sK2]
  have l30 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l29 sK2 sK1 sK2]
    conv => enter [1]; rw [← l12 sK2 sK1 sK2]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [← l30 sK2 sK1]
  have l32 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l14 sK2 X0]
    conv => enter [1]; rw [← l1 X0 X0 sK2]
  have l33 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l14 sK2 X0]
    conv => enter [1]; rw [l1 sK2 X0 X0]
  have l34 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [l33 sK2 X0]
  have l35 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 sK2 X0]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l34 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l1 sK2 X0 X0]
  have l37 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (X1 ◇ X1)) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l35 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← h54277 sK2 X1 X0]
  have l38 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l37 X0 sK0 sK1 sK0 sK0]
  have l39 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l38 sK0 sK1 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l40 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l39 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0))]
    conv => enter [1]; rw [← h54277 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l41 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l40 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l13 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l41 x z x y]

theorem Equation43_4512_54277_implies_Equation53975 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation53975 G := by
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
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 (sK1 ◇ sK2)]
  have l6 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l7 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l9 X0 X1 X2 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l12 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ (X1 ◇ X1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h54277 ((sK1 ◇ sK2) ◇ X0) X1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l13 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h54277 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l5 sK1 sK2]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← h54277 sK1 X0 sK0]
  have l15 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l13 sK2 X0 sK1]
    conv => enter [1]; rw [l10 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l16 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l12 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) X0 (X1 ◇ X1)]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l14 sK0 sK1 X0]
  have l18 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l15 sK2 X0 sK1]
    conv => enter [1]; rw [l11 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l19 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l18 sK2 X0 sK1]
    conv => enter [1]; rw [l10 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l20 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l19 sK2 X0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK2 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l21 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l20 sK2 X0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK2 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l22 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l21 sK2 X0 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l17 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l22 sK2 X0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 X0 X0 sK1]
  have l25 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 X0 X0 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l24 sK0 sK1 sK0]
    conv => enter [1]; rw [l25 sK0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l26 z x y]
  conv => enter [1]; rw [← l24 z x z]

theorem Equation43_4512_54277_implies_Equation53978 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54277 : Equation54277 G) : Equation53978 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [← h54277 sK2 X0 sK1]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l2 sK1 sK2 X0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0]
    conv => enter [1]; rw [← l0 X0 X0 sK2]
  have l5 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (X1 ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [← h54277 sK2 X1 X0]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← l5 X0 sK1 sK2 sK1]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l4 sK1 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK1]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0]
    conv => enter [1]; rw [h43 X0 (sK1 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))]
    conv => enter [1]; rw [← h54277 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X0 X1]
    conv => enter [1]; rw [← l9 sK1 sK2 X1 X0]
  intro x y z w
  conv => enter [1]; rw [l10 x y z w]
  conv => enter [1]; rw [← l4 z w z]

theorem Equation43_4512_53975_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
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
  have l8 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53975 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l9 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53975 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l11 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ (X0 ◇ X1))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l8 X2 X3 X0 X1]
    conv => enter [1]; rw [← l1 X0 (X1 ◇ ((X0 ◇ X1) ◇ X2)) (X0 ◇ X1)]
  have l12 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ ((X1 ◇ ((X0 ◇ X1) ◇ X2)) ◇ X1))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l11 X2 X3 X0 X1]
    conv => enter [1]; rw [l7 X0 (X1 ◇ ((X0 ◇ X1) ◇ X2)) X0 X1]
  have l13 : ∀ sK0 X0 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X2 ◇ (X2 ◇ X3)) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [← l10 X0 ((sK0 ◇ ((X0 ◇ sK0) ◇ X2)) ◇ sK0) sK0]
    conv => enter [1]; rw [← l12 X2 X3 X0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 X0 sK0 sK0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 X0 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 sK0]
    conv => enter [1]; rw [l13 sK0 sK0 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 sK0 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0]
  intro x y
  conv => enter [1]; rw [← l20 x y]

theorem Equation43_4512_53975_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53864 G := by
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
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h53975 (sK1 ◇ sK2) X0 sK0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [← h53975 sK1 X0 sK0]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l9 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53975 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ X0)]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK1 X1 X0]
  have l11 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l8 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) = ((sK1 ◇ X0) ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ X0) X1]
  have l13 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) = (sK1 ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l1 sK1 X1 (sK1 ◇ X0)]
  have l14 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l11 sK1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l15 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l10 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 X1 sK0]
  have l16 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK1 X0 X1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 X0 X1]
    conv => enter [1]; rw [l14 sK1 X0 X1 sK0]
  have l17 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l15 sK0 sK1 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l18 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [← l9 sK1 (sK0 ◇ X1) sK0 sK1 sK2]
    conv => enter [1]; rw [l16 sK1 sK0 X1 sK0]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK0]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2 sK0]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l9 sK0 sK1 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK0]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

theorem Equation43_4512_53975_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53867 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l2 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53975 X0 X1 X0]
    conv => enter [1]; rw [← h53975 X0 X3 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 (sK2 ◇ sK2) X0]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 (sK0 ◇ (sK2 ◇ sK2))]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l5 sK0 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation43_4512_53975_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53868 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l2 sK1 sK2 (sK1 ◇ sK2)]
  have l6 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [← l2 sK1 sK2 (sK3 ◇ sK0)]
  have l7 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) sK2]
    conv => enter [1]; rw [← l2 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK1 sK3 sK0 sK2]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK3 ◇ sK0)]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [l7 sK1 sK3 sK0 sK2]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0))]
  have l12 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l13 : ∀ sK1 sK2 sK3 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [l11 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l14 : ∀ sK1 sK2 sK3 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK1 ◇ sK2)) X0 (sK1 ◇ (sK3 ◇ sK0))]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l16 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK0 X0]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l20 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h53975 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l5 sK1 sK2]
  have l21 : ∀ sK3 sK0 X0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK3 sK0 X0 sK1 sK2
    conv => enter [1]; rw [h53975 (sK3 ◇ sK0) X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK2 sK3 sK0]
  have l22 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← h53975 sK2 X0 sK1]
  have l23 : ∀ sK3 sK0 X0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK3 sK0 X0 sK1 sK2
    conv => enter [1]; rw [l21 sK3 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l18 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0))]
  have l24 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l20 sK2 X0 sK1]
    conv => enter [1]; rw [l18 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l25 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [← h53975 (sK3 ◇ sK0) X0 sK1]
  have l26 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l22 sK1 sK2 X0]
  have l27 : ∀ sK3 sK0 X0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK3 sK0 X0 sK1 sK2
    conv => enter [1]; rw [l23 sK3 sK0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l16 sK1 sK2 sK3 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l28 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l24 sK2 X0 sK1]
    conv => enter [1]; rw [l19 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l29 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l25 sK1 sK3 sK0 X0]
  have l30 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h53975 (sK1 ◇ sK2) ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
    conv => enter [1]; rw [← l27 sK3 sK0 X0 sK1 sK2]
  have l31 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l28 sK2 X0 sK1]
    conv => enter [1]; rw [l18 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l32 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l29 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [← l30 sK1 sK2 sK3 sK0 sK1]
  have l33 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l31 sK2 X0 sK1]
    conv => enter [1]; rw [h53975 (sK1 ◇ sK2) ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
  have l34 : ∀ sK1 sK3 sK0 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l32 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l33 sK2 X0 sK1]
  have l35 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l26 sK1 sK2 sK1]
    conv => enter [1]; rw [← l34 sK1 sK3 sK0 sK2 sK1]
  have l36 : ∀ X0 X1 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK1 sK3 sK0
    conv => enter [1]; rw [h53975 X0 X1 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l29 sK1 sK3 sK0 ((sK3 ◇ sK0) ◇ X0)]
  have l37 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l36 X0 X1 sK1 X0 X0]
    conv => enter [1]; rw [← l35 sK1 sK2 X0 X0]
  have l38 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l37 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l37 sK1 (sK3 ◇ sK0) sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l38 x y z w]

theorem Equation43_4512_53975_implies_Equation53874 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53874 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK1)]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l14 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK2]
  have l15 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l5 sK1 sK2 (sK1 ◇ sK2)]
  have l16 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l17 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l18 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((X0 ◇ sK1) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ sK1) X1]
  have l19 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = ((X0 ◇ sK2) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ sK2) X1]
  have l20 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = ((X0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ sK2)) X1]
  have l21 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l20 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK1 X1 (X0 ◇ (sK1 ◇ sK2))]
  have l22 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (X1 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l19 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK1 X1 (X0 ◇ sK2)]
  have l23 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ sK1)]
  have l24 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l25 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l21 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l16 sK1 sK2 X1 X0]
  have l26 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l22 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l14 sK1 sK2 X1 X0]
  have l27 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l23 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l7 sK0 sK1 X1 X0]
  have l28 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l24 X0 X1 X2 X3]
  have l29 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l25 sK1 sK2 X0 X1]
  have l30 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l26 sK1 sK2 X0 X1]
  have l31 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l27 sK0 sK1 X0 X1]
  have l32 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l28 X0 X1 X2 X3]
  have l33 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X3 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
  have l34 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h53975 (sK1 ◇ (sK1 ◇ sK2)) X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l10 sK0 sK1 sK2]
  have l35 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h53975 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l15 sK1 sK2]
  have l36 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h53975 (sK1 ◇ sK2) X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2]
  have l37 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1, 2]; rw [h53975 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l38 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1, 2]; rw [h53975 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))]
  have l39 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1, 2]; rw [h53975 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))]
  have l40 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l39 sK0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK1 ◇ sK2)) ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l41 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l38 sK1 X0 X1 sK2]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ X0) (sK1 ◇ (sK1 ◇ sK2))]
  have l42 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l37 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0) (sK0 ◇ (sK0 ◇ sK1))]
  have l43 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l35 sK2 X0 sK1]
    conv => enter [1]; rw [l32 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l44 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l34 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l32 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l45 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [← h53975 sK2 X0 sK1]
  have l46 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← h53975 sK1 X0 sK0]
  have l47 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l40 sK0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l29 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l48 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l41 sK1 X0 X1 sK2]
    conv => enter [1]; rw [l30 sK1 sK2 ((sK1 ◇ sK2) ◇ X0) (sK1 ◇ (sK1 ◇ sK2))]
  have l49 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l42 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l31 sK0 sK1 ((sK0 ◇ sK1) ◇ X0) (sK0 ◇ (sK0 ◇ sK1))]
  have l50 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l43 sK2 X0 sK1]
    conv => enter [1]; rw [l33 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l51 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l44 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [l13 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l52 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l45 sK1 sK2 X0]
  have l53 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l46 sK0 sK1 X0]
  have l54 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l47 sK0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l32 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l55 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l48 sK1 X0 X1 sK2]
    conv => enter [1]; rw [l32 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l56 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l49 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l32 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l57 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l50 sK2 X0 sK1]
    conv => enter [1]; rw [l32 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53975 (sK1 ◇ (sK1 ◇ sK2)) sK0 sK0]
    conv => enter [1]; rw [l51 sK1 sK2 sK0 sK0]
  have l59 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h53975 (sK1 ◇ (sK1 ◇ sK2)) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) sK0]
    conv => enter [1]; rw [← l54 sK0 X0 X1 sK1 sK2]
  have l60 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) = (sK1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← l36 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) sK0]
    conv => enter [1]; rw [← l55 sK1 X0 X1 sK2]
  have l61 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l56 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l62 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l57 sK2 X0 sK1]
    conv => enter [1]; rw [l36 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
  have l63 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [← l58 sK0 sK1 sK2]
  have l64 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l60 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l61 sK0 X0 X1 sK1]
  have l65 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l52 sK1 sK2 sK1]
    conv => enter [1]; rw [l62 sK2 sK1 sK0 sK1]
  have l66 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l64 sK0 sK1 sK2 sK0 sK0]
  have l67 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l65 sK1 sK2 sK0]
    conv => enter [1]; rw [← l66 sK0 sK1 sK2]
  have l68 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
    conv => enter [1]; rw [← l67 sK1 sK2 sK0]
  have l69 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l68 sK0 sK1 sK2]
  have l70 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l69 sK1 sK2 X0 sK0]
  have l71 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l52 sK1 sK2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK2 X1 X0]
  have l72 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) = ((sK2 ◇ X0) ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l52 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ X0) X1]
  have l73 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) = (sK2 ◇ (X1 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l72 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← l1 sK2 X1 (sK2 ◇ X0)]
  have l74 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l68 sK0 sK1 sK2]
    conv => enter [1]; rw [l71 sK1 sK2 X0 X1]
  have l75 : ∀ sK2 X1 X0 sK1 : G, (sK2 ◇ (X1 ◇ (sK2 ◇ X0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK2 X1 X0 sK1
    conv => enter [1]; rw [← l73 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X1]
  have l76 : ∀ sK2 X1 X0 sK0 sK1 : G, (sK2 ◇ (X1 ◇ (sK2 ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK2 X1 X0 sK0 sK1
    conv => enter [1]; rw [l75 sK2 X1 X0 sK1]
    conv => enter [1]; rw [← l70 sK0 sK1 X1 sK2]
  have l77 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l74 sK0 sK1 sK0 X1 sK0]
    conv => enter [1]; rw [l76 sK0 X1 sK0 sK0 sK1]
  have l78 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [← l53 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l79 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l78 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l77 sK0 sK1 X0]
  have l80 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l53 sK1 sK1 sK2]
    conv => enter [1]; rw [← l79 sK1 sK2 X0 sK1]
  have l81 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l80 sK1 sK2 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l82 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53975 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l80 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))]
  have l83 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l80 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l84 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l81 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l83 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l82 x y y z]
  conv => enter [1]; rw [l84 y z x]

theorem Equation43_4512_53975_implies_Equation53877 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53877 G := by
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
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← h53975 sK1 X0 sK0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK1 X1 X0]
  have l6 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53975 X0 X1 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK1 ◇ X0)]
  have l7 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) = ((sK1 ◇ X0) ◇ (sK1 ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ X0) X1]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) = (sK1 ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l1 sK1 X1 (sK1 ◇ X0)]
  have l9 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l5 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1 X1 sK0]
  have l10 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l9 sK0 sK1 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l11 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← l1 sK2 sK2 X0]
    conv => enter [1]; rw [l6 sK2 X0 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l11 (sK0 ◇ sK1) sK2 sK0 sK1]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK0]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation43_4512_53975_implies_Equation53890 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53890 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l5 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK3]
    conv => enter [1]; rw [← h53975 sK0 X0 sK3]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← h53975 sK2 X0 sK1]
  have l7 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l5 sK3 sK0 X0]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  have l9 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h53975 X0 X1 sK0]
    conv => enter [1]; rw [← l7 sK3 sK0 (sK0 ◇ X0)]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK2 X1 X0]
  have l11 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l8 sK1 sK2 X0]
  have l12 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) = ((sK2 ◇ X0) ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l8 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ X0) X1]
  have l13 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) = (sK2 ◇ (X1 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l12 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← l1 sK2 X1 (sK2 ◇ X0)]
  have l14 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l11 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X1]
  have l15 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l10 sK1 sK2 X1 sK1]
    conv => enter [1]; rw [← l13 sK1 sK2 X1 sK1]
  have l16 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK2 X0 X1 sK1
    conv => enter [1, 2]; rw [h4512 sK2 X0 X1]
    conv => enter [1]; rw [l14 sK2 X0 X1 sK1]
  have l17 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l15 sK1 sK2 X1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X1]
  have l18 : ∀ sK3 sK0 sK1 sK2 X1 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK3 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← l9 sK2 (sK3 ◇ X1) sK3 sK0]
    conv => enter [1]; rw [l16 sK2 sK3 X1 sK1]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK1]
    conv => enter [1]; rw [← l18 sK3 sK0 sK1 sK2 sK1]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0]
  have l21 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK3 sK0 sK3 sK0]
    conv => enter [1]; rw [l19 sK3 sK0 sK1 sK2]
  have l22 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l19 sK1 sK1 sK1 sK2]
  have l23 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l22 sK1 sK2]
  have l24 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [← l21 sK3 sK0 sK1 sK2]
  have l25 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l21 sK3 sK0 sK1 sK3]
    conv => enter [1, 2]; rw [l24 sK1 sK3 sK3 sK0]
  have l26 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l25 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l26 x y z w]

theorem Equation43_4512_53975_implies_Equation53914 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53914 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l6 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l7 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l6 sK2 X0]
    conv => enter [1]; rw [← l2 sK2 X0 (sK2 ◇ sK2)]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK1 sK0]
  have l9 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l8 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l10 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h53975 X0 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l11 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53975 X0 X1 X0]
    conv => enter [1]; rw [← h53975 X0 X3 X0]
  have l12 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [← h53975 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ X1)]
  have l13 : ∀ sK2 X0 X1 : G, (sK2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ sK2)))) = (sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l12 sK2 X0 X1]
    conv => enter [1]; rw [← l2 sK2 X1 (sK2 ◇ sK2)]
  have l14 : ∀ sK2 X1 X0 : G, (sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l13 sK2 X0 X1]
    conv => enter [1, 2]; rw [l10 X0 (X0 ◇ sK2) sK2]
  have l15 : ∀ sK2 X1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = (sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1
    conv => enter [1]; rw [← l10 sK2 ((sK2 ◇ sK2) ◇ sK2) sK2]
    conv => enter [1]; rw [← l14 sK2 X1 sK2]
  have l16 : ∀ sK2 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1
    conv => enter [1]; rw [← l2 sK2 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [l15 sK2 X1]
  have l17 : ∀ sK2 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l16 sK2 X1]
  have l18 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [l17 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l19 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l17 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l18 sK2 X0]
  have l20 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l17 sK2 sK1]
    conv => enter [1]; rw [l19 sK2 X0]
  have l21 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l2 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l17 sK2 sK1]
  have l22 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← l0 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l17 sK2 sK1]
  have l23 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← l2 X0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l17 sK2 sK1]
  have l24 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l20 sK2 sK1 X0]
    conv => enter [1]; rw [l23 sK2 X0 sK1]
  have l25 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l22 sK2 X0 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l26 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l21 sK2 sK1]
    conv => enter [1]; rw [← l4 sK1 sK2 sK2]
  have l27 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l10 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1]; rw [l25 sK2 X0 sK1]
  have l28 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l26 sK2 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2]
  have l29 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l17 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l27 sK2 sK1 X0]
  have l30 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l17 sK2 sK1]
    conv => enter [1]; rw [l29 sK2 sK1 X0]
  have l31 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l21 sK2 sK1]
    conv => enter [1]; rw [← l24 sK2 sK1 sK1]
  have l32 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l31 sK2 sK1]
    conv => enter [1]; rw [l28 sK2 sK1]
  have l33 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l32 sK2 sK1]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l34 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l33 sK2 sK1 X0]
    conv => enter [1]; rw [← l2 sK2 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l35 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l34 sK2 sK1 X0]
  have l36 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l30 sK2 sK1 X0]
    conv => enter [1]; rw [l35 sK2 sK1 X0]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 (sK0 ◇ sK1) X0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
  have l38 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 X0 sK0 X1
    conv => enter [1, 2]; rw [l9 X0 sK0 sK1]
    conv => enter [1]; rw [l11 sK1 (X0 ◇ sK0) X1]
  have l39 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [l11 sK1 (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X1]
  have l40 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 sK1]
    conv => enter [1]; rw [l11 sK1 sK0 X0]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1]; rw [l11 sK1 sK0 X0]
  have l42 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l11 sK1 (sK2 ◇ sK2) X0]
  have l43 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l11 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 X1]
  have l44 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l11 sK2 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l36 sK2 sK1 sK2]
  have l45 : ∀ sK2 X1 sK1 : G, ((sK2 ◇ sK2) ◇ X1) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 sK1
    conv => enter [1]; rw [← l43 sK2 sK2 X1]
    conv => enter [1]; rw [l44 sK2 sK2 sK1]
  have l46 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l42 sK1 sK2 sK1]
    conv => enter [1]; rw [l11 sK1 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l47 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 (sK1 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l41 sK0 sK1 sK1]
  have l48 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 (sK2 ◇ sK2) sK1]
    conv => enter [1]; rw [← l40 sK1 sK0 sK1]
  have l49 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l11 sK1 (sK1 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l39 sK1 sK2 X0 sK1]
  have l50 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l11 sK1 (sK1 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l38 sK1 X0 sK0 sK1]
  have l51 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l52 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l46 sK1 sK2]
  have l53 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l47 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l54 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l51 sK0 sK1 X0]
    conv => enter [1]; rw [← l50 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l55 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l54 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l53 sK1 sK0 sK0]
  have l56 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [← l55 sK0 sK1 X0]
  have l57 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l10 (sK0 ◇ sK1) sK1 sK2]
  have l58 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l57 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 (sK0 ◇ sK1)]
  have l59 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l58 sK1 sK2 sK1]
    conv => enter [1]; rw [← l17 sK2 (sK1 ◇ sK1)]
  have l60 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l59 sK1 sK2]
    conv => enter [1]; rw [l45 sK2 (sK2 ◇ sK2) sK1]
  have l61 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l52 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l62 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l61 sK1 sK2 X0]
    conv => enter [1]; rw [← l49 sK1 sK2 X0]
  have l63 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l62 sK1 sK2 X0]
    conv => enter [1]; rw [l53 sK1 sK2 sK0]
  have l64 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l48 sK1 sK2 sK1]
    conv => enter [1]; rw [← l63 sK1 sK2 X0 sK1]
  have l65 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53975 X0 X1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l64 sK1 sK2 ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0))]
  have l66 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l45 sK2 X0 sK1]
  have l67 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l60 sK1 sK2]
    conv => enter [1]; rw [← l66 X0 sK2 sK1]
  have l68 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l65 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l2 X0 X0 X1]
  have l69 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l67 sK1 sK2 sK1]
    conv => enter [1]; rw [l68 sK1 sK2 X1 X0]
  have l70 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK0 sK1]
    conv => enter [1]; rw [l69 sK1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l70 x y z]
  conv => enter [1]; rw [← l67 y z y]

theorem Equation43_4512_53975_implies_Equation53915 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53915 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h43 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK2 sK1]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l4 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l6 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK2) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l2 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [← h53975 (sK3 ◇ sK0) X0 sK2]
  have l7 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l6 sK2 sK3 sK0 X0]
  have l8 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [h53975 X0 X1 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK2 sK3 sK0 ((sK3 ◇ sK0) ◇ X0)]
  have l9 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [← l8 sK2 (X0 ◇ sK1) sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 X0]
  have l10 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l8 sK2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l5 sK2 sK1 sK2]
  have l11 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l8 sK2 (sK3 ◇ sK0) sK2 sK3 sK0]
    conv => enter [1]; rw [l10 sK2 sK3 sK0 sK1]
  have l12 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l10 sK2 sK2 sK2 sK1]
    conv => enter [1]; rw [l9 sK2 sK2 sK2 sK1 X0]
  have l13 : ∀ sK2 sK3 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1, 1]; rw [l11 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK2) X0]
  have l14 : ∀ sK2 sK3 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [l13 sK2 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [← l12 sK2 sK1 X0]
  have l15 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [← l14 sK2 sK3 sK0 X0 sK2]
  have l16 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [h53975 X0 X1 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [← l15 sK2 sK3 sK0 ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0))]
  have l17 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [← l16 X0 X1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l1 X0 X1 X0]
  have l18 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h43 sK1 sK2]
    conv => enter [1]; rw [← l17 sK2 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l18 x y z w]

theorem Equation43_4512_53975_implies_Equation53927 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53927 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l5 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l1 sK2 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l6 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK3]
    conv => enter [1]; rw [← h53975 sK0 X0 sK3]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← h53975 sK2 X0 sK1]
  have l8 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l6 sK3 sK0 X0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l7 sK1 sK2 X0]
  have l10 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h53975 X0 X1 sK0]
    conv => enter [1]; rw [← l8 sK3 sK0 (sK0 ◇ X0)]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK1]
  have l12 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK2 X1 X0]
  have l13 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l9 sK1 sK2 X0]
  have l14 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) = ((sK2 ◇ X0) ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ X0) X1]
  have l15 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) = (sK2 ◇ (X1 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l14 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← l1 sK2 X1 (sK2 ◇ X0)]
  have l16 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l13 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X1]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l18 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l12 sK1 sK2 X1 sK1]
    conv => enter [1]; rw [← l15 sK1 sK2 X1 sK1]
  have l19 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK2 X0 X1 sK1
    conv => enter [1, 2]; rw [h4512 sK2 X0 X1]
    conv => enter [1]; rw [l16 sK2 X0 X1 sK1]
  have l20 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l17 sK1 sK2]
  have l21 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l18 sK1 sK2 X1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X1]
  have l22 : ∀ sK3 sK0 sK1 sK2 X1 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK3 sK0 sK1 sK2 X1
    conv => enter [1]; rw [← l10 sK2 (sK3 ◇ X1) sK3 sK0]
    conv => enter [1]; rw [l19 sK2 sK3 X1 sK1]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK1]
    conv => enter [1]; rw [← l22 sK3 sK0 sK1 sK2 sK1]
  have l24 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1, 2]; rw [l23 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l5 sK2 sK3 sK3 sK0]
  have l25 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1]; rw [l24 sK2 sK1 sK3 sK0]
  have l26 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l25 sK1 sK2 sK3 sK0]
  have l27 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l20 sK1 sK2]
    conv => enter [1]; rw [l26 sK1 sK2 sK3 sK0]
  have l28 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0]
  have l29 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK3 sK0 sK3 sK0]
    conv => enter [1]; rw [l23 sK3 sK0 sK1 sK2]
  have l30 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l28 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l23 sK1 sK1 sK1 sK2]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l30 sK1 sK2]
  have l32 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [← l29 sK3 sK0 sK1 sK2]
  have l33 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1, 2]; rw [l10 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l5 sK2 sK3 sK3 sK0]
  have l34 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l33 sK2 sK1 sK2 sK2]
    conv => enter [1]; rw [← l27 sK1 sK2 sK2 sK2]
  have l35 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l29 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l34 sK2 sK1]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l32 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l35 sK1 sK1 sK2 sK1]
  have l37 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l36 sK1 sK2]
    conv => enter [1, 2]; rw [l32 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l37 x y z w]

theorem Equation43_4512_53975_implies_Equation53982 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53982 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l3 X2 X0 X1]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53975 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53975 X0 X1 X0]
    conv => enter [1]; rw [← h53975 X0 X3 X0]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h53975 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l5 X0 (X0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l8 sK0 X1 X0]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X1]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l10 sK0 X1]
  have l12 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X1]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 sK2 X0]
  have l14 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l6 sK3 (sK0 ◇ sK0) sK3]
    conv => enter [1]; rw [l5 sK3 sK3 sK0]
  have l15 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 sK0]
  have l16 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l14 sK3 sK0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0) sK3]
  have l17 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0) sK1]
  have l18 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l16 sK3 sK0]
    conv => enter [1]; rw [← l12 sK0 sK3]
  have l19 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l20 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l18 sK3 sK0]
    conv => enter [1]; rw [l12 sK0 sK3]
  have l21 : ∀ sK1 sK2 sK0 sK3 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l19 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 sK0 sK3]
  have l22 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l21 sK1 sK2 sK0 sK3]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK2 sK0 sK3]
    conv => enter [1]; rw [← l20 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l23 x y z w]

theorem Equation43_4512_53975_implies_Equation53983 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53983 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l3 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l4 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK4 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK4 (sK4 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l5 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK4) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [← h53975 (sK1 ◇ sK0) X0 sK4]
  have l6 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ sK2) = (sK3 ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l3 sK2 sK3 sK2]
    conv => enter [1]; rw [← h53975 sK3 X0 sK2]
  have l7 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [h43 sK4 (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l5 sK4 sK1 sK0 X0]
  have l8 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l6 sK2 sK3 X0]
  have l9 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [h53975 X0 X1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK4 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l10 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (X0 ◇ (sK3 ◇ X1))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l8 sK2 sK3 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK3 X1 X0]
  have l11 : ∀ sK3 X0 X1 sK2 : G, (sK3 ◇ ((sK3 ◇ X0) ◇ X1)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X1) := by
    intro sK3 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l8 sK2 sK3 X0]
  have l12 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X1) = ((sK3 ◇ X0) ◇ (sK3 ◇ X1)) := by
    intro sK2 sK3 X1 X0
    conv => enter [1, 1]; rw [l8 sK2 sK3 X0]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ X0) X1]
  have l13 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X1) = (sK3 ◇ (X1 ◇ (sK3 ◇ X0))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l12 sK2 sK3 X1 X0]
    conv => enter [1]; rw [← l1 sK3 X1 (sK3 ◇ X0)]
  have l14 : ∀ sK3 X0 X1 sK2 : G, (sK3 ◇ ((sK3 ◇ X0) ◇ X1)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X1)) := by
    intro sK3 X0 X1 sK2
    conv => enter [1]; rw [l11 sK3 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK3)) X1]
  have l15 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) ◇ X1) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l10 sK2 sK3 X1 sK2]
    conv => enter [1]; rw [← l13 sK2 sK3 X1 sK2]
  have l16 : ∀ sK3 X0 X1 sK2 : G, (sK3 ◇ (sK3 ◇ (X0 ◇ X1))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X1)) := by
    intro sK3 X0 X1 sK2
    conv => enter [1, 2]; rw [h4512 sK3 X0 X1]
    conv => enter [1]; rw [l14 sK3 X0 X1 sK2]
  have l17 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X1)) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l15 sK2 sK3 X1]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK3)) X1]
  have l18 : ∀ sK4 sK1 sK0 sK2 sK3 X1 : G, (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X1)) := by
    intro sK4 sK1 sK0 sK2 sK3 X1
    conv => enter [1]; rw [← l9 sK3 (sK4 ◇ X1) sK4 sK1 sK0]
    conv => enter [1]; rw [l16 sK3 sK4 X1 sK2]
  have l19 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l17 sK2 sK3 sK2]
    conv => enter [1]; rw [← l18 sK4 sK1 sK0 sK2 sK3 sK2]
  have l20 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 sK3 sK2]
    conv => enter [1]; rw [l9 sK2 sK3 sK4 sK1 sK0]
  have l21 : ∀ sK4 sK1 sK0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l9 sK4 (sK1 ◇ sK0) sK4 sK1 sK0]
    conv => enter [1]; rw [← l19 sK2 sK3 sK4 sK1 sK0]
  have l22 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l20 sK2 sK3 sK2 sK2 sK2]
    conv => enter [1]; rw [← l19 sK2 sK3 sK2 sK2 sK2]
  have l23 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l22 sK2 sK3]
  have l24 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l23 sK2 sK3]
    conv => enter [1]; rw [← l21 sK4 sK1 sK0 sK2 sK3]
  intro x y z w u
  conv => enter [1]; rw [l24 x y z w u]

theorem Equation43_4512_53975_implies_Equation53859 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53975 : Equation53975 G) : Equation53859 G := by
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
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ sK1)]
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
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l3 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l10 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l17 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((X0 ◇ sK1) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ sK1) X1]
  have l18 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l19 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l18 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l17 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ sK1)]
  have l21 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l22 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1]
    conv => enter [1]; rw [← l11 sK0 X1 X0]
  have l23 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l20 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l12 sK0 sK1 X1 X0]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
  have l25 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l22 sK0 X0 X1]
  have l26 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l23 sK0 sK1 X0 X1]
  have l27 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l24 X0 X1 X2 X3]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53975 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l29 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53975 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0 X0]
  have l30 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1, 2]; rw [h53975 X0 X1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l31 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53975 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l32 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ sK0) ◇ X1)]
    conv => enter [1, 2]; rw [h53975 (sK0 ◇ sK0) X1 X0]
  have l33 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l32 sK0 X1 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l34 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l31 sK0 X0 X1]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l35 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l30 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0) (sK0 ◇ (sK0 ◇ sK1))]
  have l36 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l28 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h53975 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [l29 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53975 sK1 sK0 sK0]
    conv => enter [1]; rw [l29 sK1 sK0 sK0]
  have l39 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l33 sK0 X0 X1]
    conv => enter [1, 2]; rw [l29 X0 (X0 ◇ (sK0 ◇ sK0)) sK0]
  have l40 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l34 sK0 X0 X1]
    conv => enter [1]; rw [l25 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l41 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l35 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l26 sK0 sK1 ((sK0 ◇ sK1) ◇ X0) (sK0 ◇ (sK0 ◇ sK1))]
  have l42 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [← l15 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l44 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l29 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) sK0]
    conv => enter [1]; rw [← l39 sK0 X1 sK0]
  have l45 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l40 sK0 X0 X1]
    conv => enter [1]; rw [l27 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l46 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l41 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l27 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l47 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← l36 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [l42 sK0]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l36 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l49 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l44 sK0 X1]
  have l50 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l45 sK0 X0 X1]
    conv => enter [1]; rw [l29 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) sK0]
  have l51 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l46 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l29 (sK0 ◇ sK1) ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) sK0]
  have l52 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l47 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l48 sK0 sK1]
  have l54 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [← l36 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [l49 sK0 X1]
  have l55 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l50 sK0 X0 X1]
    conv => enter [1]; rw [← l15 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l56 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l51 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK1)]
  have l57 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l54 sK0 X1]
  have l58 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l36 X0 sK0 sK0]
    conv => enter [1]; rw [l55 sK0 X0 sK0]
  have l59 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l56 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l60 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l57 sK0 X1]
  have l61 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l52 sK0]
    conv => enter [1]; rw [← l58 sK0 X0]
  have l62 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l53 sK0 sK0]
    conv => enter [1]; rw [← l59 sK0 X0 X1 sK0]
  have l63 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l36 X0 sK0 sK0]
    conv => enter [1]; rw [← l62 sK0 X0 sK0]
  have l64 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l61 sK0 sK0]
    conv => enter [1]; rw [l63 sK0 sK0]
  have l65 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l64 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l66 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l64 sK0]
    conv => enter [1]; rw [l65 sK0]
  have l67 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l66 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l68 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l67 sK0 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l69 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l68 sK0 X0]
    conv => enter [1]; rw [← l60 sK0 X0]
  have l70 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l64 sK0]
    conv => enter [1]; rw [← l69 sK0 X0]
  have l71 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53975 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l70 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))]
  intro x y
  conv => enter [1]; rw [l71 x y x]

end CommutativeSemigroup5
