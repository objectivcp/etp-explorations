import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53904_implies_Equation53984 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53904 : Equation53904 G) : Equation53984 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK2 ◇ X0)]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l0 sK1 sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK2]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK2)]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l4 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK2 X0]
  have l9 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53904 X2 X3 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h53904 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h53904 X0 X2 X0]
    conv => enter [1, 2]; rw [h53904 X0 X0 X1]
  have l11 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53904 sK1 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK2]
  have l12 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53904 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l13 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53904 (sK1 ◇ sK1) X0 sK2]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK2]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53904 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ X3))]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53904 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X0)]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l15 sK1 X0]
  have l17 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l12 sK1 X0 sK2]
  have l18 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [l11 sK1 X0 sK2]
  have l19 : ∀ X2 X3 X0 : G, (X2 ◇ (X2 ◇ X3)) = (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l9 X2 X3 X0 X2]
    conv => enter [1, 2, 2]; rw [← l10 X0 X0 X2]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l16 sK1 X0]
  have l21 : ∀ X2 X3 X0 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ (X3 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l19 X2 X3 X0]
    conv => enter [1]; rw [← l14 X0 X3 X2 X0]
  have l22 : ∀ sK1 X0 X1 sK2 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = (X0 ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK1 X0 X1 sK2
    conv => enter [1, 1]; rw [l17 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) X1]
  have l23 : ∀ sK1 X0 X1 sK2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l17 sK1 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
  have l24 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l17 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [l1 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l17 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l17 sK1 (sK1 ◇ sK1) sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
  have l27 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK3 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l17 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK2]
  have l28 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [← l27 sK3 sK0 sK1 sK3]
    conv => enter [1]; rw [← l17 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK3]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2))]
  have l31 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1, 2]; rw [← l17 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l32 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l23 sK1 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l17 sK1 X1 sK1]
  have l33 : ∀ sK1 X0 X1 sK2 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X1))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l22 sK1 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X1]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l30 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l17 sK1 sK2 sK2]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l31 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ sK2) sK2]
  have l37 : ∀ sK1 X0 X1 sK2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X1))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l33 sK1 X0 X1 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK2]
  have l39 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK1 sK0
    conv => enter [1, 2]; rw [← l34 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l40 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l28 sK3 sK1 sK0]
    conv => enter [1]; rw [l39 sK3 sK1 sK0]
  have l41 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l18 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) sK2]
  have l42 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l18 sK1 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 ((sK1 ◇ sK2) ◇ sK2)]
  have l43 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l18 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [l1 sK1 sK2 ((sK1 ◇ sK2) ◇ sK2)]
  have l44 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l37 sK1 sK1 sK2 sK2]
    conv => enter [1]; rw [← l43 sK1 sK2]
  have l45 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l42 sK1 sK2]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK2]
  have l46 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l41 sK1 sK2]
  have l47 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l44 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ sK2) sK2]
  have l48 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)]
  have l49 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l47 sK1 sK2]
    conv => enter [1]; rw [← l36 sK1 sK2]
  have l50 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l48 sK1 sK2]
    conv => enter [1]; rw [l32 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l51 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK1 sK2]
    conv => enter [1]; rw [l49 sK1 sK2]
  have l52 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l50 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK2]
  have l53 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [l51 sK1 sK2]
  have l54 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l52 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 sK1 sK2]
  have l55 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l46 sK1 sK2]
    conv => enter [1]; rw [← l54 sK1 sK2]
  have l56 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l55 sK1 sK2]
  have l57 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l46 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) sK2 X0]
  have l58 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l57 sK1 X0 sK2]
  have l59 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l56 sK1 sK2]
  have l60 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l59 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l61 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l18 sK1 (sK1 ◇ sK1) sK2]
  have l62 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l17 sK1 (sK1 ◇ sK1) sK2]
  have l63 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l20 sK1 X0]
  have l64 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l63 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X1]
  have l65 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l62 sK1 sK2]
    conv => enter [1]; rw [l60 sK1 ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) sK2]
  have l66 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l61 sK1 sK2]
    conv => enter [1]; rw [l60 sK1 ((sK1 ◇ sK2) ◇ sK2) sK2]
  have l67 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l64 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l68 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l65 sK1 sK2]
    conv => enter [1]; rw [← l21 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l69 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l66 sK1 sK2]
    conv => enter [1]; rw [← l37 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2 sK2]
  have l70 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l69 sK1 sK2]
    conv => enter [1]; rw [l32 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l71 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l70 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK2]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l73 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l20 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l74 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l73 sK1 X0]
    conv => enter [1]; rw [l60 sK1 X0 sK2]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l76 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l74 sK1 X0 sK2]
  have l77 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l75 sK0 sK1]
    conv => enter [1]; rw [← h53904 sK1 sK0 sK1]
  have l78 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK0]
    conv => enter [1]; rw [← l77 sK1 sK0]
  have l79 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l78 sK1 sK0]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l79 sK0 sK1]
  have l81 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l82 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
    conv => enter [1, 1]; rw [← l80 sK0 sK1]
  have l83 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l82 sK0 sK1 X0]
  have l84 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l81 sK3 sK0 sK1]
  have l85 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l40 sK1 sK3 sK0]
    conv => enter [1]; rw [h53904 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l40 sK1 sK3 sK0]
  have l86 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53904 (sK0 ◇ (sK1 ◇ sK1)) X0 sK1]
    conv => enter [1, 2]; rw [l34 sK0 sK1]
  have l87 : ∀ sK3 sK0 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [h53904 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 sK1]
    conv => enter [1, 2]; rw [← l40 sK1 sK3 sK0]
  have l88 : ∀ X1 X2 X0 sK1 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = (X0 ◇ ((X1 ◇ X2) ◇ (sK1 ◇ sK1))) := by
    intro X1 X2 X0 sK1
    conv => enter [1]; rw [h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [h53904 (X1 ◇ X2) X0 sK1]
  have l89 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h53904 sK1 X0 sK1]
  have l90 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h53904 (sK1 ◇ sK1) sK0 sK1]
  have l91 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h53904 sK1 sK0 sK1]
  have l92 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h53904 X0 sK2 sK1]
    conv => enter [1]; rw [← l3 sK1 sK2 (X0 ◇ (sK1 ◇ sK1))]
  have l93 : ∀ sK0 sK1 sK3 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK3)) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [h53904 (sK0 ◇ (sK1 ◇ sK1)) sK3 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l94 : ∀ sK0 sK1 sK3 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK3)) = ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l93 sK0 sK1 sK3]
    conv => enter [1]; rw [← l40 sK1 sK3 sK0]
  have l95 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l67 sK1 sK2 X0]
    conv => enter [1]; rw [l92 sK1 X0 sK2]
  have l96 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK0]
  have l97 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l90 sK0 sK1]
    conv => enter [1]; rw [l60 sK1 sK0 sK2]
  have l98 : ∀ X1 X2 X0 sK1 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 X0 sK1
    conv => enter [1]; rw [l88 X1 X2 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l99 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l85 sK3 sK0 sK1]
    conv => enter [1]; rw [l60 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK2]
  have l100 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [l95 sK1 sK2 X0]
  have l101 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l96 sK0 sK1]
    conv => enter [1]; rw [l78 sK1 sK0]
  have l102 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l97 sK0 sK1 sK0]
    conv => enter [1]; rw [← l76 sK1 sK0 sK0]
  have l103 : ∀ X1 X2 X0 sK1 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 X0 sK1
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l98 X1 X2 X0 sK1]
  have l104 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l99 sK3 sK0 sK1 sK3]
    conv => enter [1]; rw [← l76 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK3]
  have l105 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l102 sK0 sK1]
    conv => enter [1, 2]; rw [l78 sK1 sK0]
  have l106 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l104 sK3 sK0 sK1]
    conv => enter [1]; rw [← l32 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l107 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l34 sK0 sK1]
    conv => enter [1]; rw [l105 sK0 sK1]
  have l108 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l20 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l106 sK1 sK3 sK0]
  have l109 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h53904 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [h53904 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l110 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l83 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l109 sK0 sK1]
  have l111 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l110 sK0 sK1]
  have l112 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l111 sK0 sK1]
    conv => enter [1]; rw [l86 sK0 sK1 (sK1 ◇ sK1)]
  have l113 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l112 sK0 sK1]
    conv => enter [1]; rw [l60 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK2]
  have l114 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l113 sK0 sK1 sK0]
    conv => enter [1]; rw [← l76 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l115 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l114 sK0 sK1]
    conv => enter [1]; rw [← l107 sK1 sK0]
  have l116 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK3 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l115 sK0 sK1]
  have l117 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l115 sK0 sK1]
  have l118 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l117 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l119 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l116 sK3 sK0 sK1]
    conv => enter [1]; rw [l28 sK3 sK1 sK0]
  have l120 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l101 sK0 sK1]
    conv => enter [1]; rw [h53904 (sK0 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l121 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l120 sK0 sK1]
    conv => enter [1, 2]; rw [l34 sK0 sK1]
  have l122 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l107 sK1 sK0]
    conv => enter [1]; rw [← l121 sK0 sK1]
  have l123 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l122 sK1 sK0]
    conv => enter [1]; rw [← l32 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l124 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l123 sK1 sK0]
  have l125 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [← l119 sK3 sK0 sK1]
    conv => enter [1]; rw [h53904 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l126 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l125 sK3 sK0 sK1]
    conv => enter [1, 2]; rw [← l40 sK1 sK3 sK0]
  have l127 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l126 sK3 sK0 sK1]
    conv => enter [1]; rw [← l32 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l128 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l32 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l127 sK3 sK0 sK1]
  have l129 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l20 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l128 sK1 sK3 sK0]
  have l130 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l89 sK1 sK0]
    conv => enter [1]; rw [h53904 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l131 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l89 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK1))]
  have l132 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l100 sK1 sK2 sK1]
    conv => enter [1]; rw [← l131 sK1 sK2]
  have l133 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l130 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l134 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l132 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK2)]
  have l135 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l107 sK1 sK0]
    conv => enter [1]; rw [← l133 sK0 sK1]
  have l136 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l134 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l137 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l135 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l138 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l124 sK1 sK0]
    conv => enter [1]; rw [l137 sK1 sK0]
  have l139 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l136 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2))]
  have l140 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l139 sK0 sK1 sK2]
  have l141 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l138 sK1 sK0]
  have l142 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l141 sK3 sK0 sK1]
    conv => enter [1]; rw [← h53904 sK1 sK3 sK1]
  have l143 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = ((sK1 ◇ sK1) ◇ sK3) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l142 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK3]
  have l144 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ sK3) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l84 sK3 sK0 sK1]
    conv => enter [1]; rw [l143 sK3 sK0 sK1]
  have l145 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ sK3) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l119 sK3 sK0 sK1]
    conv => enter [1]; rw [l144 sK3 sK0 sK1]
  have l146 : ∀ sK0 sK1 sK3 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK3) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK3]
    conv => enter [1, 2]; rw [← l145 sK1 sK3 sK0]
  have l147 : ∀ sK0 sK1 sK3 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK3) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l146 sK0 sK1 sK3]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l148 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l94 sK0 sK1 sK3]
    conv => enter [1, 2]; rw [l147 sK0 sK1 sK3]
  have l149 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l148 sK1 sK3 sK0]
    conv => enter [1]; rw [l118 sK0 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l150 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l129 sK1 sK0 sK3]
    conv => enter [1]; rw [← l149 sK1 sK3 sK0]
  have l151 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l68 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l152 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l151 sK1 sK2]
    conv => enter [1]; rw [← l37 sK1 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l153 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l152 sK1 sK2]
  have l154 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l153 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK1)]
  have l155 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l154 sK1 sK2]
    conv => enter [1, 2]; rw [l56 sK1 sK2]
  have l156 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l71 sK1 sK2]
    conv => enter [1]; rw [← l155 sK1 sK2]
  have l157 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l53 sK1 sK2]
    conv => enter [1]; rw [← l156 sK1 sK2]
  have l158 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l157 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l159 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK1]
    conv => enter [1]; rw [← l158 sK1 sK2]
  have l160 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l158 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l161 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l160 sK1 sK2 X0]
    conv => enter [1]; rw [l60 sK1 X0 sK2]
  have l162 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l76 sK1 X0 sK2]
    conv => enter [1]; rw [← l161 sK1 sK2 X0]
  have l163 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l162 sK1 X0 sK2]
  have l164 : ∀ X2 X1 X3 X0 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l21 (X2 ◇ X1) X2 X3]
    conv => enter [1, 2, 2]; rw [l21 X2 X1 X0]
  have l165 : ∀ sK3 sK0 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l21 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l150 sK1 sK3 sK0]
  have l166 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l21 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [← h53904 X0 X1 sK1]
  have l167 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [← l21 X0 sK2 sK1]
  have l168 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l21 X0 (sK1 ◇ sK2) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 X0]
  have l169 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [← l21 X2 X1 X0]
    conv => enter [1]; rw [h53904 X2 X1 sK1]
  have l170 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l21 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X2 ◇ (X1 ◇ X0)) X3]
  have l171 : ∀ sK1 X0 X1 sK2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (X1 ◇ X0))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1, 2]; rw [l21 X0 X1 sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 (sK2 ◇ (X1 ◇ X0))]
  have l172 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l171 sK1 X0 X1 sK1]
    conv => enter [1]; rw [← l58 sK1 (X1 ◇ X0) sK1]
  have l173 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l170 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X0) X3]
  have l174 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l168 X0 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l175 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l167 sK1 sK2 X0]
  have l176 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [← l166 sK1 X0 X1]
    conv => enter [1]; rw [l60 sK1 X0 sK2]
  have l177 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l21 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l165 sK3 sK0 sK1 sK1]
  have l178 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l21 sK2 sK1 X0]
    conv => enter [1]; rw [h53904 sK2 sK1 sK1]
  have l179 : ∀ X2 X1 X0 sK1 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK1 ◇ sK1))) := by
    intro X2 X1 X0 sK1
    conv => enter [1]; rw [l164 X2 X1 X2 X0]
    conv => enter [1]; rw [l169 X2 X0 (X0 ◇ (X1 ◇ X2)) sK1]
  have l180 : ∀ sK1 X0 X1 sK2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l172 sK1 X0 X1]
    conv => enter [1]; rw [← l163 sK1 sK2 (X1 ◇ X0)]
  have l181 : ∀ X0 X1 X3 sK1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ (X3 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X3 sK1
    conv => enter [1]; rw [l173 X0 X1 X3 X0]
    conv => enter [1]; rw [l169 X0 (X1 ◇ X0) X3 sK1]
  have l182 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l174 X0 sK1 sK2]
    conv => enter [1]; rw [← l163 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l183 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l76 sK1 X0 sK1]
    conv => enter [1]; rw [← l176 X1 X0 sK1 sK1]
  have l184 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l177 sK1 sK3 sK0]
    conv => enter [1]; rw [l87 sK3 sK0 sK1 (sK1 ◇ sK1)]
  have l185 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l178 X0 sK1 sK2]
  have l186 : ∀ X2 X1 X0 sK1 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (sK1 ◇ sK1)))) := by
    intro X2 X1 X0 sK1
    conv => enter [1]; rw [l179 X2 X1 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (sK1 ◇ sK1)]
  have l187 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l67 sK1 X1 X0]
    conv => enter [1]; rw [l180 sK1 X0 X1 sK2]
  have l188 : ∀ X0 X1 X3 sK1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ (X0 ◇ (X3 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X3 sK1
    conv => enter [1]; rw [l181 X0 X1 X3 sK1]
    conv => enter [1]; rw [← h4512 X1 X0 (X3 ◇ (sK1 ◇ sK1))]
  have l189 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [l76 sK1 X0 sK2]
    conv => enter [1]; rw [← l182 X0 sK1 sK2]
  have l190 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l163 sK1 sK2 X0]
    conv => enter [1]; rw [l183 sK1 X0 X1]
  have l191 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l184 sK1 sK3 sK0]
    conv => enter [1]; rw [l60 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK2]
  have l192 : ∀ X2 X1 sK1 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ X2))) := by
    intro X2 X1 sK1
    conv => enter [1]; rw [l186 X2 X1 X2 sK1]
    conv => enter [1]; rw [← l21 (sK1 ◇ sK1) (X1 ◇ X2) X2]
  have l193 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l187 sK1 X1 sK2 X0]
    conv => enter [1]; rw [← l163 sK1 sK2 X1]
  have l194 : ∀ X0 X1 X3 sK1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X3)) = (X1 ◇ (X0 ◇ (X3 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X3 sK1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X3]
    conv => enter [1]; rw [l188 X0 X1 X3 sK1]
  have l195 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l189 sK1 X0 sK2]
    conv => enter [1]; rw [← l185 sK1 sK2 X0]
  have l196 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l191 sK1 sK1 sK3 sK0]
    conv => enter [1]; rw [← l76 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l197 : ∀ X2 X1 sK1 sK2 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X2))) := by
    intro X2 X1 sK1 sK2
    conv => enter [1]; rw [l192 X2 X1 sK1]
    conv => enter [1]; rw [l60 sK1 (X1 ◇ X2) sK2]
  have l198 : ∀ X0 X1 X3 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ (X3 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X3 sK1
    conv => enter [1, 2]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l194 X0 X1 X3 sK1]
  have l199 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [l195 sK1 X0 sK2]
  have l200 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l190 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← l166 sK1 X0 sK1]
  have l201 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l108 sK1 sK1 sK1]
    conv => enter [1]; rw [← l196 sK1 sK1 sK1]
  have l202 : ∀ X2 X1 sK1 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ X2))) := by
    intro X2 X1 sK1
    conv => enter [1]; rw [l197 X2 X1 sK1 X2]
    conv => enter [1]; rw [← l76 sK1 (X1 ◇ X2) X2]
  have l203 : ∀ X1 X0 X3 sK1 : G, (X1 ◇ (X0 ◇ (X3 ◇ (sK1 ◇ sK1)))) = (X1 ◇ (X3 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 X3 sK1
    conv => enter [1]; rw [← l198 X0 X1 X3 sK1]
    conv => enter [1]; rw [l169 X0 X1 X3 sK1]
  have l204 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l200 sK1 sK2 X0]
    conv => enter [1]; rw [l199 sK1 X0 sK2]
  have l205 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l201 sK1]
    conv => enter [1]; rw [l13 sK1 sK1 sK2]
  have l206 : ∀ X2 X1 sK1 sK2 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X2))) := by
    intro X2 X1 sK1 sK2
    conv => enter [1]; rw [l202 X2 X1 sK1]
    conv => enter [1]; rw [← l163 sK1 sK2 (X1 ◇ X2)]
  have l207 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l205 sK1 sK2]
    conv => enter [1]; rw [l204 sK1 sK2 sK2]
  have l208 : ∀ X2 X1 sK1 sK2 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro X2 X1 sK1 sK2
    conv => enter [1]; rw [l206 X2 X1 sK1 sK2]
    conv => enter [1]; rw [l193 sK1 sK2 X1 X2]
  have l209 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l159 sK1 sK2]
    conv => enter [1]; rw [l207 sK1 sK2]
  have l210 : ∀ sK1 sK2 X2 X1 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) = ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) := by
    intro sK1 sK2 X2 X1
    conv => enter [1]; rw [← l204 sK1 sK2 X1]
    conv => enter [1]; rw [← l208 X2 X1 sK1 sK2]
  have l211 : ∀ sK1 sK2 X2 X1 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) := by
    intro sK1 sK2 X2 X1
    conv => enter [1]; rw [l210 sK1 sK2 X2 X1]
    conv => enter [1]; rw [← h4512 X2 X1 ((X2 ◇ X1) ◇ X2)]
  have l212 : ∀ sK1 sK2 X2 X1 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK2 X2 X1
    conv => enter [1]; rw [l211 sK1 sK2 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X2]
  have l213 : ∀ sK1 sK2 X2 X1 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) = (X2 ◇ (X2 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 X2 X1
    conv => enter [1]; rw [l212 sK1 sK2 X2 X1]
    conv => enter [1]; rw [l103 X2 X1 X2 sK1]
  have l214 : ∀ sK1 sK2 X2 X1 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) = (X2 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X2 X1
    conv => enter [1]; rw [l213 sK1 sK2 X2 X1]
    conv => enter [1]; rw [l203 X2 X2 X1 sK1]
  have l215 : ∀ sK1 sK2 X2 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X2 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X2 X1
    conv => enter [1]; rw [l209 sK1 sK2]
    conv => enter [1]; rw [l214 sK1 sK2 X2 X1]
  have l216 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l175 sK1 sK2 X0]
    conv => enter [1]; rw [h53904 X0 sK2 sK1]
  have l217 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ sK2) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [← l175 sK1 sK2 sK1]
  have l218 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK2)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ sK2)]
    conv => enter [1, 2]; rw [← l175 sK1 sK2 (sK1 ◇ sK1)]
  have l219 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l218 sK0 sK1 sK2]
  have l220 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [l217 sK1 sK2]
  have l221 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l216 sK1 sK2 X0]
    conv => enter [1]; rw [← l215 sK1 sK2 sK2 X0]
  have l222 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l219 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK2]
  have l223 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l222 sK0 sK1 sK2]
    conv => enter [1]; rw [← l38 sK0 sK1 sK2]
  have l224 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l140 sK0 sK1 sK2]
    conv => enter [1]; rw [← l223 sK0 sK1 sK2]
  have l225 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l215 sK1 sK2 (sK0 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1]; rw [← l224 sK0 sK1 sK2]
  have l226 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [← l221 sK1 sK2 X0]
    conv => enter [1]; rw [l8 sK0 sK1 sK2 X0]
  have l227 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l220 sK1 sK2]
    conv => enter [1]; rw [l221 sK1 sK2 sK1]
  have l228 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l226 sK0 sK1 sK2 X0]
  have l229 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l225 sK1 sK2 sK0]
    conv => enter [1]; rw [l228 sK0 sK1 sK2 X0]
  have l230 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l227 sK1 sK2]
    conv => enter [1]; rw [l229 sK1 sK2 sK0 X0]
  have l231 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l227 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  have l232 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l225 sK1 sK2 sK0]
    conv => enter [1]; rw [← l231 sK0 sK1 sK2]
  have l233 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l227 sK1 sK2]
    conv => enter [1]; rw [l232 sK1 sK2 sK0]
  have l234 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l233 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
  have l235 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l234 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK2 X0]
  have l236 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l230 sK1 sK2 sK1 X0]
    conv => enter [1]; rw [← l235 sK1 sK2 X0 sK1]
  have l237 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l21 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l236 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0))]
  have l238 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l237 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h53904 sK0 X0 sK1]
  intro x y z w
  conv => enter [1]; rw [l238 x y z w]

theorem Equation4512_53984_implies_Equation53904 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53984 : Equation53984 G) : Equation53904 G := by
  have l0 : ∀ X0 X1 sK2 X2 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ X2) := by
    intro X0 X1 sK2 X2
    conv => enter [1]; rw [← h53984 sK2 X2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 X2]
  have l1 : ∀ sK2 X2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X2
    conv => enter [1]; rw [h53984 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [l0 sK2 sK2 sK2 X2]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l1 sK2 X0]
  have l3 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h53984 X0 X1 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [← l1 sK2 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK2 X0]
    conv => enter [1]; rw [← h53984 sK2 sK2 sK0 sK2]
  have l5 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [l4 sK0 sK2 X0]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h53984 sK2 sK2 sK1 sK2]
  have l7 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h53984 sK2 sK2 X0 sK0]
    conv => enter [1]; rw [h53984 sK2 sK2 X1 sK0]
  have l8 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [l6 sK1 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_53904_implies_Equation54008 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53904 : Equation53904 G) : Equation54008 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53904 X2 X3 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h53904 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h53904 X0 X2 X0]
    conv => enter [1, 2]; rw [h53904 X0 X0 X1]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53904 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ X3))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53904 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ X2 X3 X0 : G, (X2 ◇ (X2 ◇ X3)) = (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l2 X2 X3 X0 X2]
    conv => enter [1, 2, 2]; rw [← l3 X0 X0 X2]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l9 : ∀ X2 X3 X0 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ (X3 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l7 X2 X3 X0]
    conv => enter [1]; rw [← l4 X0 X3 X2 X0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l8 sK0 X0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l12 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l11 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l17 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK4 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1]; rw [l18 sK1 sK0 X0]
  have l20 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l17 sK4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l21 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) = (X0 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [h53904 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0 sK0]
    conv => enter [1, 2]; rw [l20 sK4 sK1 sK0]
  have l22 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = (X0 ◇ ((X1 ◇ X2) ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [h53904 (X1 ◇ X2) X0 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53904 sK0 X0 sK0]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [← h53904 sK0 sK1 sK0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
  have l26 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l22 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l27 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l26 X1 X2 X0 sK0]
  have l28 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h53904 sK1 (sK0 ◇ sK0) sK0]
  have l29 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l28 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l30 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK4 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l25 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53904 (sK1 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1, 2]; rw [l25 sK1 sK0]
  have l32 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (((sK0 ◇ sK0) ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1, 1]; rw [l25 sK1 sK0]
  have l33 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l32 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l19 sK1 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l33 sK1 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1, 2]; rw [l25 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53904 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l40 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53904 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h53904 sK1 sK1 sK0]
  have l41 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l40 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h53904 sK1 (sK0 ◇ sK0) sK0]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l29 sK1 sK0 sK0]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l43 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h53904 sK1 X0 sK0]
    conv => enter [1]; rw [l41 sK1 X0 sK0]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1 sK0]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l25 sK1 sK0]
    conv => enter [1]; rw [l45 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l47 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l50 sK0 sK1]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l53 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l54 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l53 sK0 X0 sK1]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [l52 sK1 sK0]
  have l56 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l55 sK1 sK0]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l57 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK4 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l56 sK1 sK0]
  have l58 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l57 sK4 sK1 sK0]
    conv => enter [1]; rw [← l30 sK4 sK1 sK0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l23 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l60 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK4 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l23 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l61 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l43 sK4 sK1 sK0]
    conv => enter [1]; rw [← l60 sK4 sK1 sK0]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [l33 sK1 sK0 (sK0 ◇ sK0)]
  have l63 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l61 sK4 sK1 sK0]
    conv => enter [1]; rw [← h53904 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l64 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l63 sK4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l62 sK1 sK0]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l67 : ∀ sK1 sK0 sK4 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l64 sK4 sK1 sK0]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l69 : ∀ X2 X1 X3 X0 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l9 (X2 ◇ X1) X2 X3]
    conv => enter [1, 2, 2]; rw [l9 X2 X1 X0]
  have l70 : ∀ sK0 sK4 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (X0 ◇ (X0 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))) := by
    intro sK0 sK4 sK1 X0
    conv => enter [1]; rw [l9 (sK0 ◇ sK0) (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [l20 sK4 sK1 sK0]
  have l71 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← l9 X2 X1 X0]
    conv => enter [1]; rw [h53904 X2 X1 sK0]
  have l72 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X2 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X2 ◇ (X1 ◇ X0)) X3]
  have l73 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X1 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l9 X0 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (X1 ◇ X0))]
  have l74 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l73 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X1 ◇ X0)]
  have l75 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l72 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X0) X3]
  have l76 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ (sK0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [l9 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1]; rw [← l70 sK0 sK4 sK1 sK0]
  have l77 : ∀ X2 X1 X0 sK0 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (sK0 ◇ sK0))) := by
    intro X2 X1 X0 sK0
    conv => enter [1]; rw [l69 X2 X1 X2 X0]
    conv => enter [1]; rw [l71 X2 X0 (X0 ◇ (X1 ◇ X2)) sK0]
  have l78 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l74 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X1 ◇ X0))]
  have l79 : ∀ X0 X1 X3 sK0 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = ((X1 ◇ X0) ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X3 sK0
    conv => enter [1]; rw [l75 X0 X1 X3 X0]
    conv => enter [1]; rw [l71 X0 (X1 ◇ X0) X3 sK0]
  have l80 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ (sK0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [l76 sK0 sK4 sK1]
    conv => enter [1]; rw [← l15 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l81 : ∀ X2 X1 X0 sK0 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (sK0 ◇ sK0)))) := by
    intro X2 X1 X0 sK0
    conv => enter [1]; rw [l77 X2 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (sK0 ◇ sK0)]
  have l82 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l78 sK0 X0 X1]
    conv => enter [1]; rw [← l15 sK0 (X1 ◇ X0)]
  have l83 : ∀ X0 X1 X3 sK0 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X1 ◇ (X0 ◇ (X3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X3 sK0
    conv => enter [1]; rw [l79 X0 X1 X3 sK0]
    conv => enter [1]; rw [← h4512 X1 X0 (X3 ◇ (sK0 ◇ sK0))]
  have l84 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK4 sK1
    conv => enter [1, 2]; rw [l64 sK4 sK1 sK0]
    conv => enter [1]; rw [← l80 sK0 sK4 sK1]
  have l85 : ∀ X2 X1 sK0 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X2))) := by
    intro X2 X1 sK0
    conv => enter [1]; rw [l81 X2 X1 X2 sK0]
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) (X1 ◇ X2) X2]
  have l86 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l12 sK0 X1 X0]
    conv => enter [1]; rw [l82 sK0 X0 X1]
  have l87 : ∀ X0 X1 X3 sK0 : G, (X0 ◇ ((X0 ◇ X1) ◇ X3)) = (X1 ◇ (X0 ◇ (X3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X3 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X3]
    conv => enter [1]; rw [l83 X0 X1 X3 sK0]
  have l88 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [l84 sK0 sK4 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l89 : ∀ X2 X1 sK0 : G, ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X2))) := by
    intro X2 X1 sK0
    conv => enter [1]; rw [l85 X2 X1 sK0]
    conv => enter [1]; rw [← l15 sK0 (X1 ◇ X2)]
  have l90 : ∀ X0 X1 X3 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ (X3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X3 sK0
    conv => enter [1, 2]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l87 X0 X1 X3 sK0]
  have l91 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l64 sK4 sK1 sK0]
    conv => enter [1]; rw [← l88 sK0 sK4 sK1]
  have l92 : ∀ sK0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X2 ◇ X1) ◇ ((X2 ◇ X1) ◇ X2)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l86 sK0 X1 X2]
    conv => enter [1]; rw [← l89 X2 X1 sK0]
  have l93 : ∀ X1 X0 X3 sK0 : G, (X1 ◇ (X0 ◇ (X3 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 X3 sK0
    conv => enter [1]; rw [← l90 X0 X1 X3 sK0]
    conv => enter [1]; rw [l71 X0 X1 X3 sK0]
  have l94 : ∀ sK0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l92 sK0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 X1 ((X2 ◇ X1) ◇ X2)]
  have l95 : ∀ sK0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l94 sK0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X2]
  have l96 : ∀ sK0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X2 ◇ (X2 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l95 sK0 X1 X2]
    conv => enter [1]; rw [l27 X2 X1 X2 sK0]
  have l97 : ∀ sK0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X2 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l96 sK0 X1 X2]
    conv => enter [1]; rw [l93 X2 X2 X1 sK0]
  have l98 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l9 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0 X0]
    conv => enter [1, 2, 2]; rw [← l91 sK4 sK1 sK0]
  have l99 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1, 1]; rw [l91 sK4 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l100 : ∀ sK0 sK4 sK1 X0 : G, (sK0 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK4 sK1 X0
    conv => enter [1]; rw [← l21 sK4 sK1 sK0 sK0]
    conv => enter [1]; rw [l98 sK4 sK1 sK0 X0]
  have l101 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l99 sK4 sK1 sK0 sK0]
    conv => enter [1]; rw [l100 sK0 sK4 sK1 X0]
  have l102 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h53904 sK1 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [← l67 sK1 sK0 sK4]
  have l103 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l102 sK4 sK1 sK0]
    conv => enter [1]; rw [l29 sK1 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l104 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l103 sK4 sK1 sK0]
    conv => enter [1]; rw [← l54 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l105 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l104 sK4 sK1 sK0]
    conv => enter [1, 2]; rw [← l64 sK4 sK1 sK0]
  have l106 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l91 sK4 sK1 sK0]
    conv => enter [1]; rw [← l105 sK4 sK1 sK0]
  have l107 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l106 sK4 sK1 sK0]
    conv => enter [1]; rw [l58 sK4 sK1 sK0]
  have l108 : ∀ sK1 sK0 sK4 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [← h53904 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l106 sK4 sK1 sK0]
  have l109 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [l97 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l108 sK1 sK0 sK4]
  have l110 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK1
    conv => enter [1, 2]; rw [l64 sK4 sK1 sK0]
    conv => enter [1]; rw [l109 sK0 sK4 sK1]
  have l111 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l91 sK4 sK1 sK0]
    conv => enter [1]; rw [l110 sK0 sK4 sK1]
  have l112 : ∀ sK0 sK4 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK4 sK1
    conv => enter [1]; rw [l8 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l111 sK4 sK1 sK0]
  have l113 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l64 sK4 sK1 sK0]
    conv => enter [1]; rw [← l112 sK0 sK4 sK1]
  have l114 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l68 sK0 sK1]
  have l115 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l93 X0 X0 sK0 sK0]
    conv => enter [1]; rw [← l114 sK0 sK1 X0]
  have l116 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l115 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l117 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l51 sK0 sK0]
    conv => enter [1]; rw [← l116 X0 sK0 sK0]
  have l118 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l113 sK4 sK1 sK0]
    conv => enter [1]; rw [l117 sK0 X0]
    conv => enter [1, 2]; rw [← l113 sK4 sK1 sK0]
  have l119 : ∀ sK4 sK1 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) = (X1 ◇ (X1 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l9 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0 X1]
    conv => enter [1, 2, 2]; rw [← l118 sK4 sK1 sK0 X0]
  have l120 : ∀ sK4 sK1 sK0 X1 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [l118 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) X1]
  have l121 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l101 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [← l119 sK4 sK1 sK0 X0 sK4]
  have l122 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l120 sK4 sK1 sK0 X0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l121 sK4 sK1 sK0 X0]
  have l123 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l107 sK4 sK1 sK0]
    conv => enter [1]; rw [← l122 sK4 sK1 sK0 X0]
  have l124 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l9 X0 X1 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l123 sK4 sK1 sK0 ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X0))]
  intro x y z w u
  conv => enter [1]; rw [l124 x y z w u]

@[equational_result]
theorem Equation54008_implies_Equation53904 (G : Type*) [Magma G] (h54008 : Equation54008 G) : Equation53904 G := by
  intro x y z
  conv => enter [1]; rw [h54008 x y y x z]

theorem Equation4512_53905_implies_Equation53919 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53919 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK3 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) X0]
  have l2 : ∀ sK3 sK1 sK0 X0 X1 : G, (((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (sK3 ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK3 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← h4512 sK3 ((sK1 ◇ sK0) ◇ X0) X1]
  have l3 : ∀ sK3 sK1 sK0 X0 X1 : G, (((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (sK3 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK3 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) X0 X1]
  have l4 : ∀ sK3 sK1 sK0 X0 X1 : G, (((sK3 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l3 sK3 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK0) sK3 X0 X1]
  have l5 : ∀ sK3 sK1 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l4 sK3 sK1 sK0 X0 X1]
  have l6 : ∀ sK2 sK3 sK1 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK2 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3))) := by
    intro sK2 sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK1 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l5 sK3 sK1 sK0 X0 X1]
  have l7 : ∀ sK3 sK1 sK0 X0 X1 X2 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) ◇ X2) := by
    intro sK3 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK1 ◇ sK0)) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l5 sK3 sK1 sK0 X0 X1]
  have l8 : ∀ sK3 sK1 sK0 X0 X1 X2 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK3) ◇ X2)) := by
    intro sK3 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l7 sK3 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK3) X2]
  have l9 : ∀ sK2 sK3 sK1 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l6 sK2 sK3 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK0) sK2 (sK1 ◇ sK0) sK3]
  have l10 : ∀ sK3 sK1 sK0 X0 X1 X2 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK3 ◇ X2))) := by
    intro sK3 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l8 sK3 sK1 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK3 X2]
  have l11 : ∀ sK3 sK1 sK0 X0 X1 X2 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l10 sK3 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK0) (sK1 ◇ sK0) sK3 X2]
  have l12 : ∀ sK1 sK0 sK3 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l11 sK3 sK1 sK0 sK1 sK1 sK1]
  have l13 : ∀ sK3 sK1 sK0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [l5 sK3 sK1 sK0 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l12 sK1 sK0 sK3]
  have l14 : ∀ sK3 sK1 sK0 sK2 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l5 sK3 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 sK3 (sK1 ◇ sK0)]
  have l15 : ∀ sK2 sK3 sK1 sK0 X0 X1 X2 : G, ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK2)) ◇ X2) := by
    intro sK2 sK3 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l9 sK2 sK3 sK1 sK0 X0 X1]
  have l16 : ∀ sK2 sK3 sK1 sK0 X0 X1 X2 : G, ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK2) ◇ X2)) := by
    intro sK2 sK3 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l15 sK2 sK3 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK2) X2]
  have l17 : ∀ sK2 sK3 sK1 sK0 X0 X1 X2 : G, ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ X2))) := by
    intro sK2 sK3 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l16 sK2 sK3 sK1 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK2 X2]
  have l18 : ∀ sK1 sK0 sK2 sK3 X0 X1 X2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro sK1 sK0 sK2 sK3 X0 X1 X2
    conv => enter [1]; rw [h53905 (sK1 ◇ sK0) (sK1 ◇ sK0) sK2 X2]
    conv => enter [1]; rw [← l17 sK2 sK3 sK1 sK0 X0 X1 X2]
  have l19 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l9 sK2 sK1 sK1 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l18 sK1 sK0 sK2 sK1 sK1 sK1 sK1]
  have l20 : ∀ sK3 sK1 sK0 sK2 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK2)) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l13 sK3 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0 sK2]
  have l21 : ∀ sK3 sK1 sK0 sK2 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK2)) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l14 sK3 sK1 sK0 sK2]
    conv => enter [1]; rw [l20 sK3 sK1 sK0 sK2]
  have l22 : ∀ sK3 sK1 sK0 sK2 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l21 sK3 sK1 sK0 sK2]
    conv => enter [1]; rw [← l9 sK2 sK3 sK1 sK0 sK1 sK2]
  have l23 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro X1 sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [← h53905 sK1 X1 sK0 X0]
  have l24 : ∀ X1 sK1 sK2 sK3 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X1 sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) X1 (sK3 ◇ (sK1 ◇ sK0)) X0]
  have l25 : ∀ sK2 sK3 sK1 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK2))) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [h53905 (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) X0 sK2 sK2]
    conv => enter [1, 2]; rw [l9 sK2 sK3 sK1 sK0 sK2 sK2]
  have l26 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l27 : ∀ sK1 sK0 sK3 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK3 X0
    conv => enter [1]; rw [← l5 sK3 sK1 sK0 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h53905 X0 (sK3 ◇ (sK1 ◇ sK0)) sK1 sK1]
  have l28 : ∀ sK3 sK1 sK0 X0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [l5 sK3 sK1 sK0 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l27 sK1 sK0 sK3 X0]
  have l29 : ∀ sK2 sK3 sK1 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [l25 sK2 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK0) X0 (sK1 ◇ sK0) sK2]
  have l30 : ∀ X1 sK1 sK2 sK3 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0))) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro X1 sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l24 X1 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l26 sK1 sK2 (sK1 ◇ sK2) X1]
  have l31 : ∀ sK3 sK1 sK0 sK2 X0 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l14 sK3 sK1 sK0 sK2]
    conv => enter [1]; rw [l28 sK3 sK1 sK0 X0]
  have l32 : ∀ sK2 sK3 sK1 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [l29 sK2 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [l23 (sK1 ◇ sK0) sK1 sK0 X0]
  have l33 : ∀ sK1 sK2 sK3 sK0 X1 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X1 X0
    conv => enter [1]; rw [← h53905 sK2 sK1 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l30 X1 sK1 sK2 sK3 sK0 X0]
  have l34 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h53905 sK1 sK1 sK1 sK0]
    conv => enter [1]; rw [← l32 sK2 sK3 sK1 sK0 X0]
  have l35 : ∀ sK1 sK2 sK3 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X1
    conv => enter [1]; rw [l33 sK1 sK2 sK3 sK0 X1 sK1]
    conv => enter [1]; rw [← h53905 sK1 X1 (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) sK1]
  have l36 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [l9 sK2 sK1 sK1 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l37 : ∀ sK1 sK2 sK3 sK0 X1 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l35 sK1 sK2 sK3 sK0 X1]
  have l38 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l36 sK1 sK0 sK2]
    conv => enter [1]; rw [← l9 sK2 sK3 sK1 sK0 sK1 sK2]
  have l39 : ∀ sK1 sK2 sK3 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X1
    conv => enter [1]; rw [h4512 sK1 sK2 (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l37 sK1 sK2 sK3 sK0 X1]
  have l40 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l38 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l22 sK3 sK1 sK0 sK2]
  have l41 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l39 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l40 sK1 sK3 sK0 sK2]
  have l42 : ∀ sK3 sK1 sK0 sK2 X0 X1 : G, ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK3 ◇ (sK1 ◇ sK0))))) := by
    intro sK3 sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l31 sK3 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK3 ◇ (sK1 ◇ sK0)))]
  have l43 : ∀ X1 X0 sK3 sK1 sK0 sK2 : G, (X1 ◇ (X1 ◇ X0)) = ((sK3 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK3 sK1 sK0 sK2
    conv => enter [1]; rw [h53905 X1 X0 (X0 ◇ X1) (sK3 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l42 sK3 sK1 sK0 sK2 X0 X1]
  have l44 : ∀ X1 X0 sK1 sK2 sK3 sK0 : G, (X1 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l43 X1 X0 sK3 sK1 sK0 sK2]
    conv => enter [1]; rw [← l41 sK1 sK2 sK3 sK0]
  have l45 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l44 sK3 X0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h53905 sK3 X0 sK1 sK0]
  have l46 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← l39 sK1 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [l45 sK1 sK2 sK3 sK0 X0]
  intro x y z w
  conv => enter [1]; rw [l46 x y y z w]

theorem Equation4512_53919_implies_Equation53905 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53919 : Equation53919 G) : Equation53905 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l0 sK1 sK2 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l2 sK1 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h53919 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 sK1 X0]
  have l5 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) ◇ X1) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1) ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [l4 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1) X1]
  have l6 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) ◇ X1) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ X1))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 X1]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) ◇ X1) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h53919 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X1]
    conv => enter [1]; rw [← l6 sK1 sK2 sK3 sK0 X0 X1]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) X1]
  have l9 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK3 ◇ sK0)) X0 X1]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 (sK1 ◇ sK1)]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l4 sK1 sK2 sK3 sK0 X0]
  have l13 : ∀ sK3 sK0 X1 sK1 X0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK0 X1 sK1 X0
    conv => enter [1]; rw [h53919 (sK3 ◇ sK0) X1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK3 ◇ sK0) X0]
  have l14 : ∀ sK1 sK3 sK0 X1 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X1)) = (X1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK3 sK0 X1 sK2 X0
    conv => enter [1]; rw [h53919 (sK1 ◇ (sK3 ◇ sK0)) X1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l15 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l12 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h53919 (sK1 ◇ (sK3 ◇ sK0)) X0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l16 : ∀ sK2 sK1 sK3 sK0 X1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0))) := by
    intro sK2 sK1 sK3 sK0 X1 X0
    conv => enter [1]; rw [h53919 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK3 sK0 X0]
  have l17 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53919 X0 sK1 (sK1 ◇ sK2) X1]
  have l18 : ∀ sK1 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53919 X0 sK1 (sK3 ◇ sK0) X1]
  have l19 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h53919 X0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK3 ◇ sK0)) sK1]
  have l20 : ∀ sK2 sK1 sK3 sK0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X1)) := by
    intro sK2 sK1 sK3 sK0 X1
    conv => enter [1]; rw [l16 sK2 sK1 sK3 sK0 X1 sK2]
    conv => enter [1]; rw [← h53919 (sK1 ◇ (sK3 ◇ sK0)) X1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l21 : ∀ sK2 sK1 sK3 sK0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0 X1
    conv => enter [1]; rw [l20 sK2 sK1 sK3 sK0 X1]
    conv => enter [1]; rw [← l13 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0)) sK1 X1]
  have l22 : ∀ sK1 sK3 sK0 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1)) := by
    intro sK1 sK3 sK0 sK2 X1
    conv => enter [1]; rw [h53919 sK1 (sK3 ◇ sK0) (sK3 ◇ sK0) (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l21 sK2 sK1 sK3 sK0 X1]
  have l23 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l22 sK1 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [← l14 sK1 sK3 sK0 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK2 sK1]
  have l24 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l23 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l18 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l25 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l24 sK1 sK3 sK0]
    conv => enter [1]; rw [← l15 sK1 sK1 sK2 sK3 sK0]
  have l26 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l25 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [← h53919 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1)) (sK3 ◇ sK0)]
  have l27 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l26 sK1 sK3 sK0]
  have l28 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l27 sK1 X0 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l29 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l28 sK1 X0 sK3 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
  have l30 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53919 sK1 sK1 sK1 X0]
    conv => enter [1]; rw [← l29 sK1 sK3 sK0 X0]
  have l31 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l26 sK1 sK3 sK0]
    conv => enter [1]; rw [l30 sK1 sK3 sK0 X0]
  have l32 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53919 (sK1 ◇ (sK3 ◇ sK0)) X0 sK1 sK1]
    conv => enter [1, 2]; rw [← l31 sK1 sK3 sK0 sK1]
  have l33 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [h53919 X0 sK1 (sK1 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1]; rw [← l31 sK1 sK3 sK0 (X0 ◇ X0)]
  have l34 : ∀ sK3 sK0 sK1 X0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l13 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0)) sK1 X0]
    conv => enter [1]; rw [l32 sK1 sK3 sK0 X0]
  have l35 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53919 sK1 (sK3 ◇ sK0) (sK3 ◇ sK0) (sK3 ◇ sK0)]
    conv => enter [1]; rw [l34 sK3 sK0 sK1 X0]
  have l36 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l19 sK1 sK2 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l37 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0 ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l19 sK1 sK2 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
  have l38 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l37 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l17 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK3 ◇ sK0))]
  have l39 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ X1))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l36 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h53919 sK1 X1 (X0 ◇ X1) (sK1 ◇ sK2)]
  have l40 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l38 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l33 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK3 sK0]
  have l41 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l39 sK1 sK2 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [← h53919 sK1 X0 sK1 sK1]
  have l42 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [← l41 sK1 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [l40 sK1 sK1 sK3 sK0]
  have l43 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l42 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l35 sK1 sK1 sK1 X0]
    conv => enter [1, 2]; rw [← l42 sK1 sK2 sK1 sK1]
  have l44 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h53919 X0 X1 X2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l43 sK1 sK2 X0]
  have l45 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l44 X0 X1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l43 sK1 sK2 X0]
  have l46 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l43 sK1 sK2 X1]
    conv => enter [1]; rw [← l45 X0 X1 sK1 sK2]
  have l47 : ∀ sK1 sK2 X1 X2 X0 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro sK1 sK2 X1 X2 X0 X3
    conv => enter [1]; rw [l46 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h53919 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l47 x y y x z w]

theorem Equation4512_53905_implies_Equation53928 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53928 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK3 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) X0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK3 sK0 sK1 X0 X1 : G, (((sK3 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK3 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK3 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← h4512 sK3 ((sK0 ◇ sK1) ◇ X0) X1]
  have l4 : ∀ sK3 sK0 sK1 X0 X1 : G, (((sK3 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK3 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK3 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 X1]
  have l5 : ∀ sK3 sK0 sK1 X0 X1 : G, (((sK3 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK3)) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK3 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK1) sK3 X0 X1]
  have l6 : ∀ sK3 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK3)) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l5 sK3 sK0 sK1 X0 X1]
  have l7 : ∀ sK2 sK3 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK3))) := by
    intro sK2 sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l6 sK3 sK0 sK1 X0 X1]
  have l8 : ∀ sK2 sK3 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK2 sK3 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK1) sK2 (sK0 ◇ sK1) sK3]
  have l9 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK3 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l6 sK3 sK0 sK1 sK3 (sK0 ◇ sK1)]
  have l10 : ∀ X1 sK1 sK2 sK3 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X1 sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) X1 (sK3 ◇ (sK0 ◇ sK1)) X0]
  have l11 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l12 : ∀ sK2 sK3 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK3 ◇ (sK0 ◇ sK1)) sK2 X0 X1]
  have l13 : ∀ sK0 sK1 sK3 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK3)) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3 X0
    conv => enter [1]; rw [← l6 sK3 sK0 sK1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53905 X0 (sK3 ◇ (sK0 ◇ sK1)) sK0 sK0]
  have l14 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2)))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 sK0 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53905 X0 (sK3 ◇ (sK0 ◇ sK1)) X1 X2]
  have l15 : ∀ sK0 sK1 sK2 X0 sK3 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0 sK3
    conv => enter [1]; rw [← l8 sK2 sK3 sK0 sK1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53905 X0 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK0 sK0]
  have l16 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [l8 sK2 sK3 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X0 sK3]
  have l17 : ∀ X0 sK1 sK2 sK3 sK0 X1 X2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 sK1 sK2 sK3 sK0 X1 X2
    conv => enter [1]; rw [h53905 X0 (sK1 ◇ sK2) X0 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l14 sK1 sK2 sK3 sK0 X0 X1 X2]
  have l18 : ∀ sK3 sK0 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l6 sK3 sK0 sK1 sK3 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l13 sK0 sK1 sK3 X0]
  have l19 : ∀ sK2 sK3 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK3)) := by
    intro sK2 sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK2 sK3 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l6 sK3 sK0 sK1 (sK3 ◇ (sK0 ◇ sK1)) sK2]
  have l20 : ∀ X1 sK1 sK2 sK3 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0))) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro X1 sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l10 X1 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l11 sK1 sK2 (sK1 ◇ sK2) X1]
  have l21 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [h53905 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK1 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l17 X0 sK1 sK2 sK3 sK0 sK2 sK2]
  have l22 : ∀ sK3 sK0 sK1 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l9 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK3 sK0 sK1 X0]
  have l23 : ∀ sK2 sK3 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l19 sK2 sK3 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l6 sK3 sK0 sK1 sK3 (sK0 ◇ sK1)]
  have l24 : ∀ sK1 sK2 sK3 sK0 X1 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X1 X0
    conv => enter [1]; rw [← h53905 sK2 sK1 sK3 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l20 X1 sK1 sK2 sK3 sK0 X0]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l8 sK2 sK0 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [l21 sK2 sK0 sK0 sK1 X0]
  have l26 : ∀ sK2 sK3 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l23 sK2 sK3 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l9 sK3 sK0 sK1 sK2]
  have l27 : ∀ sK1 sK2 sK3 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X1
    conv => enter [1]; rw [l24 sK1 sK2 sK3 sK0 X1 sK1]
    conv => enter [1]; rw [← h53905 sK1 X1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK1]
  have l28 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [l8 sK2 sK3 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [l25 sK0 sK1 sK2 X0]
  have l29 : ∀ sK1 sK2 sK3 sK0 X1 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l27 sK1 sK2 sK3 sK0 X1]
  have l30 : ∀ sK1 sK2 sK3 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X1
    conv => enter [1]; rw [h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l29 sK1 sK2 sK3 sK0 X1]
  have l31 : ∀ sK3 sK0 sK1 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l26 sK2 sK3 sK0 sK1 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← h53905 X0 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK3 sK3]
  have l32 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK3 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ sK1))]
  have l33 : ∀ sK3 sK0 sK1 sK2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK3 sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l22 sK3 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l34 : ∀ X1 X0 sK3 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X0)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h53905 X1 X0 (X0 ◇ X1) (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l33 sK3 sK0 sK1 sK2 X0 X1]
  have l35 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 sK1 sK2 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l36 : ∀ X1 X0 sK2 sK3 sK0 sK1 : G, (X1 ◇ (X1 ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l34 X1 X0 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK3 sK0 sK1 sK2 sK2]
  have l37 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h53905 sK2 sK1 sK3 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l35 sK3 sK0 sK1 sK2]
  have l38 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l37 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l22 sK3 sK0 sK1 sK2 sK2]
  have l39 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l38 sK1 sK2 sK3 sK0]
  have l40 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l39 sK1 sK2 sK3 sK0]
  have l41 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l31 sK3 sK0 sK1 sK2 sK1]
  have l42 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l41 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l22 sK3 sK0 sK1 sK2 sK2]
  have l43 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l40 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l42 sK1 sK2 sK3 sK0]
  have l44 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l16 sK2 sK3 sK0 sK1 sK1]
  have l45 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l43 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l44 sK1 sK2 sK3 sK0]
  have l46 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l45 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l28 sK2 sK3 sK0 sK1 sK1]
  have l47 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l30 sK1 sK2 sK1 sK1 sK2]
    conv => enter [1]; rw [l30 sK1 sK2 sK1 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [l30 sK1 sK2 sK1 sK1 sK2]
  have l48 : ∀ X0 X1 X2 X3 sK0 sK1 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 X2 X3 sK0 sK1
    conv => enter [1]; rw [← h53905 X1 X0 X2 X3]
    conv => enter [1]; rw [h53905 X1 X0 sK0 sK1]
  have l49 : ∀ sK3 sK0 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK3 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h53905 (sK0 ◇ sK1) X0 sK0 sK1]
  have l50 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h53905 X0 (X1 ◇ X2) sK0 sK1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (sK0 ◇ sK1))]
  have l51 : ∀ sK2 sK3 sK0 sK1 X1 X2 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1 X1 X2 X0
    conv => enter [1]; rw [← l36 X0 (X1 ◇ X2) sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l50 X0 X1 X2 sK0 sK1]
  have l52 : ∀ sK0 sK1 sK3 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK3)) = (sK3 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3 X0
    conv => enter [1]; rw [← l6 sK3 sK0 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l49 sK3 sK0 sK1 X0]
  have l53 : ∀ X0 sK3 sK0 sK1 sK2 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h53905 sK3 X0 sK0 sK1]
    conv => enter [1]; rw [l36 sK3 X0 sK2 sK3 sK0 sK1]
  have l54 : ∀ sK2 sK3 sK0 sK1 X1 X2 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK0 sK1 X1 X2
    conv => enter [1]; rw [l51 sK2 sK3 sK0 sK1 X1 X2 sK2]
    conv => enter [1]; rw [l48 X1 X2 sK2 (sK0 ◇ sK1) sK0 sK1]
  have l55 : ∀ sK0 sK1 sK3 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK3)) = (sK3 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK3 X0
    conv => enter [1]; rw [l52 sK0 sK1 sK3 X0]
    conv => enter [1]; rw [l48 sK3 X0 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0 sK1]
  have l56 : ∀ sK1 sK2 sK3 sK0 X1 X2 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0 X1 X2
    conv => enter [1]; rw [l40 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l54 sK2 sK3 sK0 sK1 X1 X2]
  have l57 : ∀ sK3 sK0 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l6 sK3 sK0 sK1 sK3 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l55 sK0 sK1 sK3 X0]
  have l58 : ∀ sK1 sK2 X1 X2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X1 X2 sK0
    conv => enter [1]; rw [← l46 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l56 sK1 sK2 sK1 sK0 X1 X2]
  have l59 : ∀ sK3 sK0 sK1 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK3 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l9 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l57 sK3 sK0 sK1 X0]
  have l60 : ∀ sK1 sK2 X1 X2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X1 X2 sK0
    conv => enter [1]; rw [l47 sK1 sK2]
    conv => enter [1]; rw [l58 sK1 sK2 X1 X2 sK0]
  have l61 : ∀ sK2 sK3 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (sK3 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [← l22 sK3 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [l59 sK3 sK0 sK1 sK2 X0]
  have l62 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l60 sK1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← l61 sK2 sK3 sK0 sK1 sK1]
  have l63 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l62 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l53 X0 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l63 x y y z w]

theorem Equation4512_53928_implies_Equation53905 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53928 : Equation53928 G) : Equation53905 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
  have l3 : ∀ sK3 sK0 X0 X1 X2 sK1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ (((sK3 ◇ sK0) ◇ X0) ◇ X1)) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0))) := by
    intro sK3 sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h53928 ((sK3 ◇ sK0) ◇ X0) X1 X2 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK3 ◇ sK0) X0]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h53928 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK2 sK3 sK0]
  have l5 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [h53928 X0 X4 X3 X3]
    conv => enter [1, 2]; rw [h53928 X3 X0 X1 X2]
  have l6 : ∀ sK3 sK0 X1 X2 X0 : G, ((sK3 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X0))) = (sK3 ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 (X1 ◇ (X2 ◇ X0))]
    conv => enter [1, 2]; rw [← h53928 X0 sK0 X1 X2]
  have l7 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (X1 ◇ X0)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [h53928 X0 sK1 sK2 X1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X1 ◇ X0)]
  have l8 : ∀ X0 sK1 sK3 sK0 X1 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro X0 sK1 sK3 sK0 X1
    conv => enter [1]; rw [h53928 X0 sK1 (sK3 ◇ sK0) X1]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ sK0) (X1 ◇ X0)]
  have l9 : ∀ X0 sK2 sK1 sK3 sK0 X1 : G, (X0 ◇ (X0 ◇ sK2)) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X1 ◇ X0)) := by
    intro X0 sK2 sK1 sK3 sK0 X1
    conv => enter [1]; rw [h53928 X0 sK2 (sK1 ◇ (sK3 ◇ sK0)) X1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK3 ◇ sK0)) (X1 ◇ X0)]
  have l10 : ∀ sK3 sK0 X1 X0 : G, ((sK3 ◇ sK0) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h53928 X0 sK3 sK0 X1]
  have l11 : ∀ sK1 sK3 sK0 X1 X2 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X1 ◇ (X2 ◇ X0))) = (sK1 ◇ (X0 ◇ (X0 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) (X1 ◇ (X2 ◇ X0))]
    conv => enter [1, 2]; rw [← h53928 X0 (sK3 ◇ sK0) X1 X2]
  have l12 : ∀ sK1 sK2 sK3 sK0 X1 X2 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X1 ◇ (X2 ◇ X0)))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 sK0 (X1 ◇ (X2 ◇ X0))]
    conv => enter [1, 2]; rw [← h53928 X0 (sK1 ◇ (sK3 ◇ sK0)) X1 X2]
  have l13 : ∀ sK1 sK2 sK3 sK0 X1 X2 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X1 ◇ (X2 ◇ X0)))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h53928 (sK1 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK2) X0 X0]
  have l14 : ∀ sK1 sK3 sK0 X1 X2 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X1 ◇ (X2 ◇ X0))) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [l11 sK1 sK3 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h53928 (sK3 ◇ sK0) sK1 X0 X0]
  have l15 : ∀ sK3 sK0 X1 X2 X0 : G, ((sK3 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X0))) = (sK0 ◇ (sK0 ◇ sK3)) := by
    intro sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [l6 sK3 sK0 X1 X2 X0]
    conv => enter [1]; rw [← h53928 sK0 sK3 X0 X0]
  have l16 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [← h53928 (sK1 ◇ (sK3 ◇ sK0)) X0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l17 : ∀ X1 X2 sK1 sK3 sK0 X0 : G, (X1 ◇ (X2 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0))) = ((sK3 ◇ sK0) ◇ (X0 ◇ (((sK3 ◇ sK0) ◇ X0) ◇ X1))) := by
    intro X1 X2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l3 sK3 sK0 X0 X1 X2 sK1]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK0) X0 (((sK3 ◇ sK0) ◇ X0) ◇ X1)]
  have l18 : ∀ sK1 sK2 sK3 sK0 X1 X2 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X1 ◇ (X2 ◇ X0)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [l13 sK1 sK2 sK3 sK0 X1 X2 X0]
    conv => enter [1]; rw [← l8 (sK1 ◇ sK2) sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
  have l19 : ∀ sK1 sK3 sK0 X1 X2 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X1 ◇ (X2 ◇ X0))) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [l14 sK1 sK3 sK0 X1 X2 X0]
    conv => enter [1]; rw [l10 sK3 sK0 (sK3 ◇ sK0) sK1]
  have l20 : ∀ sK1 sK3 sK0 X0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0))) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [← l16 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0)]
  have l21 : ∀ X1 X2 sK1 sK3 sK0 X0 : G, (X1 ◇ (X2 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0))) = (sK0 ◇ (sK0 ◇ sK3)) := by
    intro X1 X2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [l17 X1 X2 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [l15 sK3 sK0 X0 ((sK3 ◇ sK0) ◇ X0) X1]
  have l22 : ∀ sK1 sK2 sK3 sK0 X1 X2 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X1 ◇ (X2 ◇ X0)))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [l18 sK1 sK2 sK3 sK0 X1 X2 X0]
    conv => enter [1]; rw [← l7 sK1 sK1 sK2 (sK1 ◇ sK2)]
  have l23 : ∀ sK1 sK3 sK0 X0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)))) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l20 sK1 sK3 sK0 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0]
  have l24 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l22 sK1 sK2 sK3 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← l5 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 sK1 sK1 sK1]
  have l25 : ∀ sK1 sK3 sK0 X0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l23 sK1 sK3 sK0 X0 sK2]
    conv => enter [1]; rw [← l5 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l24 sK1 sK2 sK1 sK1]
  have l27 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK3 sK0 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [← l25 sK1 sK3 sK0 X0 sK2]
  have l28 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53928 sK1 X0 sK1 sK1]
    conv => enter [1, 2]; rw [← l26 sK1 sK2]
  have l29 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK2 sK3 sK0 (sK1 ◇ (sK1 ◇ X0))]
    conv => enter [1, 2]; rw [← h53928 X0 (sK1 ◇ (sK3 ◇ sK0)) sK1 sK1]
  have l30 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l1 sK1 sK2 sK3 sK0 ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [← l27 sK1 sK2 sK3 sK0 X0]
  have l31 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53928 X0 X1 (sK1 ◇ (X0 ◇ X0)) (sK1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← l27 sK1 sK2 X0 X0 X0]
  have l32 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l27 sK1 sK2 sK3 sK0 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h53928 X0 (sK1 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK3 ◇ sK0)) sK1]
  have l33 : ∀ sK1 sK3 sK0 X0 X1 X2 sK2 : G, (((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ (((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1)) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK3 sK0 X0 X1 X2 sK2
    conv => enter [1]; rw [h53928 ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) X1 X2 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l27 sK1 sK2 sK3 sK0 X0]
  have l34 : ∀ sK1 sK2 X1 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 sK3 sK0 X0
    conv => enter [1, 1]; rw [l27 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ sK0)) ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) X1]
  have l35 : ∀ sK1 sK2 X1 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 sK3 sK0 X0
    conv => enter [1]; rw [l34 sK1 sK2 X1 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK3 ◇ sK0)) X0 X1]
  have l36 : ∀ sK1 sK3 sK0 X0 X1 X2 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK3 sK0 X0 X1 X2 sK2
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK3 ◇ sK0)) X0 (((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l33 sK1 sK3 sK0 X0 X1 X2 sK2]
  have l37 : ∀ sK0 sK3 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK3)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [← l21 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 sK3 sK0 sK0]
    conv => enter [1]; rw [l30 sK1 sK2 sK3 sK0 sK0]
  have l38 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l29 sK1 sK2 sK3 sK1 sK1]
    conv => enter [1]; rw [l19 sK1 sK3 sK1 sK1 sK1 (sK1 ◇ (sK3 ◇ sK1))]
  have l39 : ∀ sK1 sK2 X1 sK3 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 X1 sK3
    conv => enter [1]; rw [l35 sK1 sK2 X1 sK3 sK1 sK1]
    conv => enter [1]; rw [l19 sK1 sK3 sK1 (sK1 ◇ (sK3 ◇ sK1)) sK1 X1]
  have l40 : ∀ sK1 sK3 X1 X2 sK2 : G, (sK1 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK3 X1 X2 sK2
    conv => enter [1]; rw [← l19 sK1 sK3 sK1 sK1 ((sK1 ◇ (sK3 ◇ sK1)) ◇ sK1) X1]
    conv => enter [1]; rw [l36 sK1 sK3 sK1 sK1 X1 X2 sK2]
  have l41 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l37 sK1 sK3 sK1 sK2]
    conv => enter [1]; rw [l31 sK1 sK3 sK1 sK2]
  have l42 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l38 sK1 sK2 sK3]
    conv => enter [1]; rw [l28 sK1 sK3 sK2]
  have l43 : ∀ sK1 sK2 X1 sK3 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1 sK3
    conv => enter [1]; rw [l39 sK1 sK2 X1 sK3]
    conv => enter [1]; rw [l28 sK1 sK3 sK2]
  have l44 : ∀ X1 X2 sK1 sK2 sK3 : G, (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 X2 sK1 sK2 sK3
    conv => enter [1]; rw [← l40 sK1 sK3 X1 X2 sK2]
    conv => enter [1]; rw [l28 sK1 sK3 sK2]
  have l45 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l43 sK1 sK2 X1 sK1]
    conv => enter [1]; rw [← l41 sK1 sK2 sK1]
  have l46 : ∀ sK1 sK2 X1 X2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X1 X2
    conv => enter [1]; rw [l41 sK1 sK2 sK1]
    conv => enter [1]; rw [← l44 X1 X2 sK1 sK2 sK1]
  have l47 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l32 sK1 sK2 (sK1 ◇ sK2) sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l48 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l45 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l47 sK1 sK2 sK1 sK1]
  have l49 : ∀ sK0 sK3 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK3)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK3 sK1 sK2]
    conv => enter [1]; rw [l48 sK1 sK2]
  have l50 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [← l31 sK3 sK3 sK1 sK2]
    conv => enter [1]; rw [l49 sK3 sK3 sK1 sK2]
  have l51 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l42 sK1 sK2 sK1]
  have l52 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53928 X0 X1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [l45 sK1 sK2 (X0 ◇ X0)]
  have l53 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l52 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l46 sK1 sK2 X1 (sK1 ◇ sK2)]
  have l54 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l53 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l48 sK1 sK2]
  have l55 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l51 sK1 sK2]
    conv => enter [1]; rw [← l54 X0 X1 sK1 sK2]
  have l56 : ∀ sK1 sK2 X1 X2 X3 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (X3 ◇ X0))) := by
    intro sK1 sK2 X1 X2 X3 X0
    conv => enter [1]; rw [l55 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h53928 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l56 x y y x z w]

theorem Equation4512_53905_implies_Equation53932 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53932 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, ((sK2 ◇ sK3) ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) (sK4 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, ((sK2 ◇ sK3) ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK2 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l0 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l2 : ∀ sK4 sK1 sK0 X0 X1 : G, (((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (sK4 ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK4 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← h4512 sK4 ((sK1 ◇ sK0) ◇ X0) X1]
  have l3 : ∀ sK4 sK1 sK0 X0 X1 : G, (((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (sK4 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK4 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) X0 X1]
  have l4 : ∀ sK4 sK1 sK0 X0 X1 : G, (((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK4)) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l3 sK4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK0) sK4 X0 X1]
  have l5 : ∀ sK4 sK1 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK4)) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK4 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l4 sK4 sK1 sK0 X0 X1]
  have l6 : ∀ sK3 sK4 sK1 sK0 X0 X1 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK3 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK4))) := by
    intro sK3 sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK4 ◇ (sK1 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l5 sK4 sK1 sK0 X0 X1]
  have l7 : ∀ sK4 sK1 sK0 X0 X1 X2 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK4)) ◇ X2) := by
    intro sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK4 ◇ (sK1 ◇ sK0)) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l5 sK4 sK1 sK0 X0 X1]
  have l8 : ∀ sK4 sK1 sK0 X0 X1 X2 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK4) ◇ X2)) := by
    intro sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l7 sK4 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK4) X2]
  have l9 : ∀ sK3 sK4 sK1 sK0 X0 X1 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) := by
    intro sK3 sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l6 sK3 sK4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK0) sK3 (sK1 ◇ sK0) sK4]
  have l10 : ∀ sK4 sK1 sK0 X0 X1 X2 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK4 ◇ X2))) := by
    intro sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l8 sK4 sK1 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK4 X2]
  have l11 : ∀ sK4 sK1 sK0 X0 X1 X2 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l10 sK4 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK0) (sK1 ◇ sK0) sK4 X2]
  have l12 : ∀ sK1 sK0 sK4 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK4)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [← l5 sK4 sK1 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l11 sK4 sK1 sK0 sK1 sK1 sK1]
  have l13 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l5 sK4 sK1 sK0 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l12 sK1 sK0 sK4]
  have l14 : ∀ sK4 sK1 sK0 sK2 sK3 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l5 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l5 sK4 sK1 sK0 sK4 (sK1 ◇ sK0)]
  have l15 : ∀ sK3 sK4 sK1 sK0 X0 X1 X2 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) ◇ X2) := by
    intro sK3 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l9 sK3 sK4 sK1 sK0 X0 X1]
  have l16 : ∀ sK3 sK4 sK1 sK0 X0 X1 X2 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ sK3) ◇ X2)) := by
    intro sK3 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l15 sK3 sK4 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK3) X2]
  have l17 : ∀ sK3 sK4 sK1 sK0 X0 X1 X2 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK3 ◇ X2))) := by
    intro sK3 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l16 sK3 sK4 sK1 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK3 X2]
  have l18 : ∀ sK1 sK0 sK3 sK4 X0 X1 X2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro sK1 sK0 sK3 sK4 X0 X1 X2
    conv => enter [1]; rw [h53905 (sK1 ◇ sK0) (sK1 ◇ sK0) sK3 X2]
    conv => enter [1]; rw [← l17 sK3 sK4 sK1 sK0 X0 X1 X2]
  have l19 : ∀ sK1 sK0 sK3 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← l9 sK3 sK1 sK1 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l18 sK1 sK0 sK3 sK1 sK1 sK1 sK1]
  have l20 : ∀ sK4 sK1 sK0 sK3 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) := by
    intro sK4 sK1 sK0 sK3
    conv => enter [1]; rw [l13 sK4 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0 sK3]
  have l21 : ∀ sK4 sK1 sK0 sK2 sK3 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l14 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l20 sK4 sK1 sK0 sK3]
  have l22 : ∀ sK4 sK1 sK0 sK2 sK3 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l21 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l9 sK3 sK4 sK1 sK0 sK2 sK3]
  have l23 : ∀ X1 sK3 sK4 sK1 sK0 X0 : G, (X1 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK3 ◇ (sK3 ◇ X1)) := by
    intro X1 sK3 sK4 sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK3 (sK4 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← h53905 sK3 X1 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l24 : ∀ X1 sK2 sK3 sK4 sK1 sK0 X0 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0))) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X1)) := by
    intro X1 sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1, 2]; rw [← l1 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK2 ◇ sK3) X1 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l25 : ∀ sK3 sK4 sK1 sK0 X0 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3))) := by
    intro sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [h53905 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0 sK3 sK3]
    conv => enter [1, 2]; rw [l9 sK3 sK4 sK1 sK0 sK3 sK3]
  have l26 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK3 sK2 X0 X1]
  have l27 : ∀ sK1 sK0 sK4 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK4)) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK4 X0
    conv => enter [1]; rw [← l5 sK4 sK1 sK0 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h53905 X0 (sK4 ◇ (sK1 ◇ sK0)) sK1 sK1]
  have l28 : ∀ sK2 sK3 sK4 sK1 sK0 X0 X1 X2 : G, (sK2 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ X2)))) = ((sK2 ◇ sK3) ◇ (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [← l1 sK2 sK3 sK4 sK1 sK0 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53905 X0 (sK4 ◇ (sK1 ◇ sK0)) X1 X2]
  have l29 : ∀ X0 sK2 sK3 sK4 sK1 sK0 X1 X2 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) = (sK2 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 sK2 sK3 sK4 sK1 sK0 X1 X2
    conv => enter [1]; rw [h53905 X0 (sK2 ◇ sK3) X0 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l28 sK2 sK3 sK4 sK1 sK0 X0 X1 X2]
  have l30 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l5 sK4 sK1 sK0 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l27 sK1 sK0 sK4 X0]
  have l31 : ∀ sK3 sK4 sK1 sK0 X0 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l25 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK0) X0 (sK1 ◇ sK0) sK3]
  have l32 : ∀ X1 sK2 sK3 sK4 sK1 sK0 X0 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0))) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro X1 sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l24 X1 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [l26 sK2 sK3 (sK2 ◇ sK3) X1]
  have l33 : ∀ sK3 sK4 sK1 sK0 sK2 X0 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK4 sK1 sK0 sK2 X0
    conv => enter [1]; rw [h53905 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) sK2 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l29 X0 sK2 sK3 sK4 sK1 sK0 sK3 sK3]
  have l34 : ∀ sK4 sK1 sK0 sK2 sK3 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l14 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l30 sK4 sK1 sK0 X0]
  have l35 : ∀ sK1 sK0 sK3 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK3 X0
    conv => enter [1]; rw [← l9 sK3 sK1 sK1 sK0 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l31 sK3 sK1 sK1 sK0 X0]
  have l36 : ∀ sK2 sK3 sK4 sK1 sK0 X1 X0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK2 sK3 sK4 sK1 sK0 X1 X0
    conv => enter [1]; rw [← h53905 sK3 sK2 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l32 X1 sK2 sK3 sK4 sK1 sK0 X0]
  have l37 : ∀ sK1 sK0 sK3 X0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK3)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK3 X0 sK2
    conv => enter [1]; rw [← l9 sK3 sK1 sK1 sK0 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK2]
    conv => enter [1]; rw [l33 sK3 sK1 sK1 sK0 sK2 X0]
  have l38 : ∀ sK3 sK4 sK1 sK0 sK2 X0 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK3 sK4 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l9 sK3 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l35 sK1 sK0 sK3 X0]
  have l39 : ∀ sK2 sK3 sK4 sK1 sK0 X1 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 sK4 sK1 sK0 X1
    conv => enter [1]; rw [l36 sK2 sK3 sK4 sK1 sK0 X1 sK2]
    conv => enter [1]; rw [← h53905 sK2 X1 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) sK2]
  have l40 : ∀ sK3 sK4 sK1 sK0 sK2 X0 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK4 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l9 sK3 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l37 sK1 sK0 sK3 X0 sK2]
  have l41 : ∀ sK4 sK1 sK0 sK2 sK3 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK4 sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l22 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l38 sK3 sK4 sK1 sK0 sK2 X0]
  have l42 : ∀ sK2 sK3 sK4 sK1 sK0 X1 : G, ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 sK4 sK1 sK0 X1
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l39 sK2 sK3 sK4 sK1 sK0 X1]
  have l43 : ∀ sK4 sK1 sK0 sK2 sK3 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK4 sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l22 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l40 sK3 sK4 sK1 sK0 sK2 X0]
  have l44 : ∀ sK2 sK3 sK4 sK1 sK0 X1 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 sK4 sK1 sK0 X1
    conv => enter [1]; rw [h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l42 sK2 sK3 sK4 sK1 sK0 X1]
  have l45 : ∀ sK4 sK1 sK0 sK2 sK3 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l34 sK4 sK1 sK0 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
  have l46 : ∀ sK4 sK1 sK0 sK2 sK3 X0 X1 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK4 sK1 sK0 sK2 sK3 X0 X1
    conv => enter [1]; rw [l34 sK4 sK1 sK0 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l47 : ∀ X1 X0 sK4 sK1 sK0 sK2 sK3 : G, (X1 ◇ (X1 ◇ X0)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h53905 X1 X0 (X0 ◇ X1) (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l46 sK4 sK1 sK0 sK2 sK3 X0 X1]
  have l48 : ∀ sK4 sK1 sK0 sK2 sK3 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro sK4 sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l45 sK4 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l26 sK2 sK3 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l49 : ∀ X1 X0 sK3 sK4 sK1 sK0 : G, (X1 ◇ (X1 ◇ X0)) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X0 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l47 X1 X0 sK4 sK1 sK0 X1 sK3]
    conv => enter [1]; rw [l34 sK4 sK1 sK0 X1 sK3 sK3]
  have l50 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h53905 sK3 sK2 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l48 sK4 sK1 sK0 sK2 sK3]
  have l51 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l50 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l34 sK4 sK1 sK0 sK2 sK3 sK3]
  have l52 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l51 sK2 sK3 sK4 sK1 sK0]
  have l53 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l52 sK2 sK3 sK4 sK1 sK0]
  have l54 : ∀ sK4 sK1 sK0 sK2 sK3 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ X0)) = ((sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK4 sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [h4512 (sK4 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK3) X0]
    conv => enter [1, 1]; rw [l34 sK4 sK1 sK0 sK2 sK3 sK3]
  have l55 : ∀ sK4 sK1 sK0 sK2 sK3 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ X0)) = (sK3 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK4 sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l54 sK4 sK1 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l56 : ∀ sK4 sK1 sK0 sK2 sK3 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ X0)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK4 sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l55 sK4 sK1 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [l23 sK3 sK3 sK4 sK1 sK0 X0]
  have l57 : ∀ sK4 sK1 sK0 sK2 sK3 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ X0)) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l56 sK4 sK1 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [l49 sK3 sK3 sK3 sK4 sK1 sK0]
  have l58 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l53 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l57 sK4 sK1 sK0 sK2 sK3 X0]
  have l59 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK4)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l58 sK2 sK3 sK4 sK1 sK0 sK2]
    conv => enter [1]; rw [l5 sK4 sK1 sK0 (sK2 ◇ sK3) sK2]
  have l60 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l59 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l41 sK4 sK1 sK0 sK2 sK3 sK4]
  have l61 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0) = (sK3 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1, 1]; rw [l53 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l62 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l61 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [l23 sK3 sK3 sK4 sK1 sK0 X0]
  have l63 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l62 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [l49 sK3 sK3 sK3 sK4 sK1 sK0]
  have l64 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l53 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l63 sK2 sK3 sK4 sK1 sK0 X0]
  have l65 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l64 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l66 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l60 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l43 sK4 sK1 sK0 sK2 sK3 sK2]
  have l67 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l44 sK2 sK3 sK2 sK2 sK2 sK3]
    conv => enter [1]; rw [l44 sK2 sK3 sK2 sK2 sK2 (sK3 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l44 sK2 sK3 sK2 sK2 sK2 sK3]
  have l68 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1, 1]; rw [← l44 sK2 sK3 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l69 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l68 sK2 sK3 X0 sK4 sK1 sK0]
    conv => enter [1]; rw [← l65 sK2 sK3 sK4 sK1 sK0 X0]
  have l70 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l69 sK2 sK3 X0 sK2 sK2 sK2]
    conv => enter [1]; rw [l66 sK2 sK3 sK2 sK2 sK2]
  have l71 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l67 sK2 sK3]
    conv => enter [1]; rw [← l70 sK2 sK3 X0]
  have l72 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l71 sK2 sK3 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← h53905 X0 (sK2 ◇ (sK2 ◇ sK3)) sK2 sK2]
  have l73 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l72 sK2 sK3 sK2]
    conv => enter [1]; rw [l49 sK2 (sK2 ◇ (sK2 ◇ sK3)) sK3 sK4 sK1 sK0]
  have l74 : ∀ X0 sK4 sK1 sK0 sK3 : G, (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← h53905 sK4 X0 sK1 sK0]
    conv => enter [1]; rw [l49 sK4 X0 sK3 sK4 sK1 sK0]
  have l75 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l73 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l74 X0 sK4 sK1 sK0 sK3]
  intro x y z w u
  conv => enter [1]; rw [l75 x y y z w u]

theorem Equation4512_53932_implies_Equation53905 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53932 : Equation53932 G) : Equation53905 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK2 ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [h53932 sK1 (sK2 ◇ X0) sK1 sK1 sK2]
  have l1 : ∀ X0 sK1 sK2 X2 X3 X4 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro X0 sK1 sK2 X2 X3 X4
    conv => enter [1]; rw [← h53932 X0 X0 sK1 sK1 sK2]
    conv => enter [1]; rw [h53932 X0 X0 X2 X3 X4]
  have l2 : ∀ X1 X0 sK1 sK2 X2 X3 X4 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro X1 X0 sK1 sK2 X2 X3 X4
    conv => enter [1, 2]; rw [← h53932 X1 X0 sK1 sK1 sK2]
    conv => enter [1]; rw [h53932 X1 (X1 ◇ X0) X2 X3 X4]
  have l3 : ∀ X1 X0 sK1 sK2 X2 X3 X4 : G, (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X1 X0 sK1 sK2 X2 X3 X4
    conv => enter [1]; rw [l2 X1 X0 sK1 sK2 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ (X3 ◇ X4))]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
  have l5 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [l1 X1 sK1 sK2 X0 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l3 X1 X0 X1 X1 sK1 sK1 sK2]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l4 sK1 sK2 X0]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← l5 sK2 sK1 sK2 X0]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53932 sK1 sK2 sK1 sK1 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2 X0]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1]; rw [h53932 (sK1 ◇ (sK1 ◇ sK2)) X0 X1 sK1 sK2]
  have l10 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 X1 sK1]
    conv => enter [1]; rw [← h53932 X0 X1 sK1 sK1 sK2]
  have l11 : ∀ sK1 sK2 X1 X2 X3 X4 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK1 sK2 X1 X2 X3 X4
    conv => enter [1]; rw [l10 sK1 sK2 sK1 X1]
    conv => enter [1]; rw [h53932 sK1 X1 X2 X3 X4]
  intro x y z w
  conv => enter [1]; rw [l11 x y y x z w]

theorem Equation4512_53905_implies_Equation53940 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53940 G := by
  have l0 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK0 X0]
  have l1 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK2 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ X0) X1]
  have l2 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK2 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l3 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 sK0 sK2 X0 X1]
  have l4 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l3 sK2 sK0 X0 X1]
  have l5 : ∀ sK1 sK2 sK0 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1, 1]; rw [l0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ X0) X1]
  have l6 : ∀ sK1 sK2 sK0 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l7 : ∀ sK1 sK2 sK0 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 sK0 (sK1 ◇ sK2) X0 X1]
  have l8 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l7 sK1 sK2 sK0 X0 X1]
  have l9 : ∀ sK2 sK0 X0 X1 X2 X3 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK0) ◇ (X2 ◇ X3)) := by
    intro sK2 sK0 X0 X1 X2 X3
    conv => enter [1]; rw [l4 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← l4 sK2 sK0 X2 X3]
  have l10 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK2 sK0 sK1 sK2 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK0]
  have l11 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l10 sK2 sK0 sK1]
  have l12 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) (sK1 ◇ sK2)]
  have l13 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [h53905 X0 X1 (sK1 ◇ sK2) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK2 sK0]
  have l14 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) X1 sK0 X0]
  have l15 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l16 : ∀ sK1 sK2 sK0 X0 X1 X2 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (sK1 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53905 X0 (sK2 ◇ sK0) X1 X2]
  have l17 : ∀ sK1 sK2 sK0 X0 X1 X2 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0 X1 X2
    conv => enter [1]; rw [l16 sK1 sK2 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h53905 X0 sK1 X0 (sK2 ◇ sK0)]
  have l18 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l14 X1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l15 sK1 sK2 (sK1 ◇ sK2) X1]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l8 sK1 sK2 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l17 sK1 sK2 sK0 X0 sK0 sK0]
  have l20 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l18 X1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l13 sK2 sK1 sK1 sK2 sK0]
  have l21 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l19 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l13 sK0 (sK1 ◇ sK2) sK1 sK2 sK0]
  have l22 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l20 X1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK2 ◇ sK0))]
  have l23 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l21 X0 sK1 sK2 sK0]
  have l24 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l12 sK1 sK2 sK0]
    conv => enter [1]; rw [l23 sK1 sK2 sK0 X0]
  have l25 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [h53905 X0 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l24 sK1 sK2 sK0 X0]
  have l26 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l25 X0 X1 sK1 sK2 sK0]
    conv => enter [1]; rw [l22 X1 sK1 sK2 sK0 (sK1 ◇ sK2)]
  have l27 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l26 sK1 sK2 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK2 ◇ sK0)) X0]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l26 sK1 sK2 sK1 sK2 sK1]
    conv => enter [1]; rw [← l26 (sK1 ◇ sK2) (sK1 ◇ (sK2 ◇ sK1)) sK1 sK2 sK1]
    conv => enter [1, 2]; rw [← l26 sK1 sK2 sK1 sK2 sK1]
  have l29 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l27 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [l15 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l30 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l29 sK1 sK2 X0]
    conv => enter [1]; rw [l13 sK2 sK1 sK1 sK2 sK0]
  have l31 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l30 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK2 ◇ sK0))]
  have l32 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l31 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l26 sK2 sK0 sK1 sK2 sK0]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l34 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [l32 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l35 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l26 sK1 sK2 sK1 sK2 sK1]
    conv => enter [1]; rw [← l26 sK1 (sK1 ◇ sK2) sK1 sK2 sK1]
  have l36 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [← h53905 X1 X0 sK1 sK2]
    conv => enter [1]; rw [l26 X1 X0 sK1 sK2 sK0]
  have l37 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l36 X0 X1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l26 sK2 sK0 sK1 sK2 sK0]
  have l38 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l37 X0 X1 sK1 sK2 X0]
    conv => enter [1]; rw [← l34 sK1 sK2 X0]
  have l39 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l35 sK1 sK2]
    conv => enter [1]; rw [← l38 X0 X1 sK1 sK2]
  have l40 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l39 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← h53905 X0 X1 sK1 sK2]
  have l41 : ∀ sK1 sK2 X1 X0 X2 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X1 X0 X2 X3
    conv => enter [1]; rw [l40 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l41 x y z x y w]

theorem Equation4512_53940_implies_Equation53905 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53940 : Equation53940 G) : Equation53905 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
  have l3 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK3 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ X0) X1]
  have l4 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK3 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l3 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l5 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l4 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h53940 sK0 X0 sK3 X1]
  have l6 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l5 sK3 sK0 X0 X1]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l2 sK1 sK2 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l9 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l8 sK1 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0]
  have l10 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h53940 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 X0]
    conv => enter [1]; rw [← l9 sK1 sK2 sK3 sK0 X0]
  have l11 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0 X0]
  have l12 : ∀ sK3 sK0 X0 X1 X2 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [l6 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l6 sK3 sK0 X0 X2]
  have l13 : ∀ sK3 sK0 sK1 X0 X1 : G, ((sK3 ◇ sK0) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = ((sK3 ◇ sK0) ◇ (sK1 ◇ X1)) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK1 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [l12 sK3 sK0 sK1 ((sK3 ◇ sK0) ◇ X0) X1]
  have l14 : ∀ sK3 sK0 sK1 X0 : G, ((sK3 ◇ sK0) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l13 sK3 sK0 sK1 X0 sK3]
    conv => enter [1]; rw [l12 sK3 sK0 sK1 sK3 (sK3 ◇ sK0)]
  have l15 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1]; rw [l12 sK3 sK0 sK3 (sK0 ◇ X0) sK0]
  have l16 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h53940 sK1 sK1 X0 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l17 : ∀ sK1 sK2 sK3 sK0 X1 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X1 X0
    conv => enter [1]; rw [h53940 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0)) X1 X0]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK3 sK0 X0]
  have l18 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l11 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h53940 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK3 ◇ sK0)) X0 X0]
  have l19 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53940 sK2 X0 sK1 X1]
  have l20 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53940 (sK1 ◇ sK2) X0 sK1 X1]
  have l21 : ∀ sK1 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53940 (sK3 ◇ sK0) X0 sK1 X1]
  have l22 : ∀ sK3 sK0 sK2 sK1 X0 X1 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l12 sK3 sK0 sK2 (sK1 ◇ (sK3 ◇ sK0)) (X0 ◇ (X1 ◇ sK3))]
    conv => enter [1, 2]; rw [← h53940 X0 X1 sK2 sK3]
  have l23 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) = ((sK3 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l12 sK3 sK0 sK3 sK0 (X0 ◇ (X1 ◇ sK3))]
    conv => enter [1, 2]; rw [← h53940 X0 X1 sK3 sK3]
  have l24 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h53940 (sK1 ◇ (sK3 ◇ sK0)) X0 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l25 : ∀ sK3 sK0 sK1 sK2 X0 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l12 sK3 sK0 sK1 sK2 (X0 ◇ sK3)]
    conv => enter [1]; rw [← h53940 sK1 X0 (sK3 ◇ sK0) sK3]
  have l26 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l12 sK3 sK0 sK2 (sK1 ◇ (sK3 ◇ sK0)) (X0 ◇ sK3)]
    conv => enter [1]; rw [← h53940 sK2 X0 (sK3 ◇ sK0) sK3]
  have l27 : ∀ sK3 sK0 sK1 X0 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [← l14 sK3 sK0 sK1 (X0 ◇ sK3)]
    conv => enter [1]; rw [← h53940 (sK1 ◇ (sK3 ◇ sK0)) X0 (sK3 ◇ sK0) sK3]
  have l28 : ∀ sK3 sK0 sK1 sK2 X0 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l12 sK3 sK0 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l27 sK3 sK0 sK1 X0]
  have l29 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [← l6 sK3 sK0 X0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← l23 sK3 sK0 X0 sK0]
  have l30 : ∀ sK0 X0 sK3 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 X0 sK3 sK2 sK1
    conv => enter [1]; rw [← l6 sK3 sK0 X0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← l22 sK3 sK0 sK2 sK1 X0 sK0]
  have l31 : ∀ sK1 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l21 sK1 sK3 sK0 X0 X1]
    conv => enter [1]; rw [l15 sK3 sK0 X0]
  have l32 : ∀ sK1 sK2 X0 X1 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 X1 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l26 sK3 sK0 sK2 sK1 X0]
  have l33 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 X0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l20 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK3 ◇ sK0))]
  have l34 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h53940 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 sK1]
    conv => enter [1]; rw [← l17 sK1 sK2 sK3 sK0 sK1 sK1]
  have l35 : ∀ sK3 sK0 sK1 sK2 X0 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l25 sK3 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l16 X0 sK1 sK2 sK3 sK0]
  have l36 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l28 sK3 sK0 sK1 sK2 sK1]
  have l37 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← l30 sK0 sK3 sK3 sK2 sK1]
    conv => enter [1]; rw [l29 sK0 sK3 sK3]
  have l38 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l32 sK1 sK2 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) sK3 sK0]
    conv => enter [1]; rw [← l33 X0 sK1 sK2 sK3 sK0]
  have l39 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l34 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l32 sK1 sK2 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0)) sK3 sK0]
  have l40 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK3 sK0 sK1 sK2 sK3]
    conv => enter [1]; rw [← l38 sK3 sK0 sK2 sK1 sK3]
  have l41 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l39 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l37 sK3 sK0 sK2 sK1]
  have l42 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l36 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l40 sK3 sK0 sK1 sK2]
  have l43 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l41 sK1 sK2 sK3 sK0]
  have l44 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [← l43 sK1 sK2 sK3 sK0]
  have l45 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK3 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l44 sK1 sK3 sK0 sK2]
  have l46 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l36 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l45 sK3 sK0 sK1 sK2]
  have l47 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [l37 sK3 sK0 sK2 sK1]
  have l48 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l47 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ sK0) (sK3 ◇ sK0)]
  have l49 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l46 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l48 sK1 sK3 sK0 sK2]
  have l50 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [← l31 sK3 sK3 sK0 X0 (X1 ◇ sK3)]
    conv => enter [1]; rw [← h53940 X0 X1 (sK3 ◇ (sK3 ◇ sK0)) sK3]
  have l51 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l43 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l50 sK3 sK0 X0 X1]
  have l52 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK1 (sK3 ◇ sK0) sK3 sK0]
    conv => enter [1]; rw [← l32 sK1 sK2 sK3 sK0 sK3 sK0]
  have l53 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l52 sK1 sK2 sK3 sK0]
  have l54 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l42 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l32 sK1 sK2 sK1 sK2 sK3 sK0]
  have l55 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l32 sK1 sK2 sK1 sK2 sK3 sK0]
  have l56 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l55 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l57 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK3 sK0 sK3 sK0]
    conv => enter [1]; rw [← l32 sK1 sK2 sK1 sK2 sK3 sK0]
  have l58 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l53 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l57 sK1 sK2 sK3 sK0]
  have l59 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l56 sK1 sK3 sK0 sK2]
  have l60 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l54 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l59 sK1 sK2 sK1 sK1]
  have l61 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l58 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l60 sK1 sK2]
  have l62 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l58 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l63 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l61 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l62 sK1 sK2 sK3 sK0]
  have l64 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l63 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l25 sK3 sK0 sK1 sK2 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l65 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (sK1 ◇ sK2))) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ sK1))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [← h53940 (X1 ◇ X2) sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ sK1)]
  have l66 : ∀ X0 sK1 X1 X2 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 X1 X2 sK2
    conv => enter [1]; rw [h53940 X0 sK1 (X1 ◇ X2) sK2]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (sK1 ◇ sK2))]
  have l67 : ∀ sK1 sK2 sK3 sK0 X1 X2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [l51 sK1 sK2 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [l66 X0 sK1 X1 X2 sK2]
  have l68 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (sK1 ◇ sK2))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ sK1)))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l65 X0 X1 X2 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 sK1]
  have l69 : ∀ sK3 sK0 sK1 sK2 X0 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l25 sK3 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [h53940 sK1 sK1 X0 sK2]
  have l70 : ∀ sK1 sK2 X1 X2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X1 X2 X0
    conv => enter [1]; rw [← l54 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l67 sK1 sK2 sK1 sK1 X1 X2 X0]
  have l71 : ∀ X2 X1 X0 sK1 sK2 : G, (X2 ◇ (X2 ◇ X1)) = (X0 ◇ ((X1 ◇ X2) ◇ (sK1 ◇ sK2))) := by
    intro X2 X1 X0 sK1 sK2
    conv => enter [1]; rw [h53940 X2 X1 X1 (X2 ◇ sK1)]
    conv => enter [1]; rw [← l68 X0 X1 X2 sK1 sK2]
  have l72 : ∀ sK1 sK2 sK3 sK0 X1 X2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0 X1 X2 X0
    conv => enter [1]; rw [l58 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l70 sK1 sK2 X1 X2 X0]
  have l73 : ∀ X2 X1 X0 sK1 sK2 : G, (X2 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK2)))) := by
    intro X2 X1 X0 sK1 sK2
    conv => enter [1]; rw [l71 X2 X1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (sK1 ◇ sK2)]
  have l74 : ∀ sK1 sK2 sK3 sK0 X2 X1 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X2 ◇ (X2 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X2 X1
    conv => enter [1]; rw [l72 sK1 sK2 sK3 sK0 sK1 X1 X2]
    conv => enter [1]; rw [← l73 X2 X1 sK1 sK1 sK2]
  have l75 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l69 X0 X0 sK1 sK2 X0]
    conv => enter [1]; rw [l69 X0 X0 sK1 sK2 X1]
  have l76 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l64 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l69 sK3 sK0 sK1 sK2 X0]
  have l77 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l75 X0 sK1 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ (sK1 ◇ sK2))]
  have l78 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l74 sK1 sK2 sK1 sK1 sK1 sK2]
    conv => enter [1]; rw [l76 sK1 sK2 sK1 sK1 X0]
  have l79 : ∀ X0 sK1 sK2 sK3 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 sK1 sK2 sK3 sK0 X1 X2
    conv => enter [1]; rw [l77 X0 sK1 sK2 (sK3 ◇ sK0) X1]
    conv => enter [1]; rw [l12 sK3 sK0 X1 (sK1 ◇ (sK1 ◇ sK2)) X2]
  have l80 : ∀ sK1 sK2 sK3 sK0 X1 X2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK3 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro sK1 sK2 sK3 sK0 X1 X2
    conv => enter [1]; rw [l78 sK1 sK2 sK1]
    conv => enter [1]; rw [l79 sK1 sK1 sK2 sK3 sK0 X1 X2]
  have l81 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l80 sK1 sK2 sK1 sK1 X0 (X1 ◇ sK1)]
    conv => enter [1]; rw [← h53940 X0 X1 (sK1 ◇ sK1) sK1]
  have l82 : ∀ sK1 sK2 X2 X0 X1 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro sK1 sK2 X2 X0 X1 X3
    conv => enter [1]; rw [l81 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h53940 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l82 x y y x z w]

theorem Equation4512_53905_implies_Equation53949 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53949 G := by
  have l0 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK0 sK1 X0 X1]
  have l1 : ∀ X0 X1 X2 X3 sK1 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 X2 X3 sK1 sK0
    conv => enter [1]; rw [← h53905 X1 X0 X2 X3]
    conv => enter [1]; rw [h53905 X1 X0 sK1 sK0]
  have l2 : ∀ X2 X0 X1 sK1 sK0 : G, (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ X1) ◇ (X2 ◇ (sK1 ◇ sK0))) := by
    intro X2 X0 X1 sK1 sK0
    conv => enter [1]; rw [h53905 X2 X2 X0 X1]
    conv => enter [1]; rw [h53905 X2 (X0 ◇ X1) sK1 sK0]
  have l3 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [h53905 X0 X0 sK1 sK0]
    conv => enter [1]; rw [h53905 X0 (sK1 ◇ sK0) X1 X2]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53905 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l3 X0 sK1 sK0 X0 X0]
    conv => enter [1]; rw [l0 sK1 sK0 X0 (X0 ◇ X0)]
  have l6 : ∀ X2 X0 X1 sK1 sK0 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK0)))) := by
    intro X2 X0 X1 sK1 sK0
    conv => enter [1]; rw [l2 X2 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l5 X0 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l8 : ∀ X2 X0 X1 sK1 sK0 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro X2 X0 X1 sK1 sK0
    conv => enter [1]; rw [l6 X2 X0 X1 sK1 sK0]
    conv => enter [1]; rw [l1 X0 X1 X2 (sK1 ◇ sK0) sK1 sK0]
  have l9 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← l8 X0 X0 X1 sK1 sK0]
    conv => enter [1]; rw [l7 X0 sK1 sK0]
  have l10 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [h53905 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [l9 sK3 sK2 sK1 sK0]
  have l11 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← l9 sK4 sK2 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l11 x y z w u]

@[equational_result]
theorem Equation53949_implies_Equation53905 (G : Type*) [Magma G] (h53949 : Equation53949 G) : Equation53905 G := by
  have l0 : ∀ X0 sK1 sK2 X1 X2 X3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro X0 sK1 sK2 X1 X2 X3
    conv => enter [1, 2]; rw [h53949 sK1 sK2 X0 sK1 sK2]
    conv => enter [1]; rw [h53949 X0 (sK1 ◇ (sK1 ◇ sK2)) X1 X2 X3]
  have l1 : ∀ sK1 sK2 X1 X0 X2 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X1 X0 X2 X3
    conv => enter [1]; rw [h53949 sK1 sK2 X0 sK1 sK2]
    conv => enter [1]; rw [l0 X0 sK1 sK2 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l1 x y y x z w]

theorem Equation4512_53905_implies_Equation53953 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53953 G := by
  have l0 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) X1 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l4 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0))) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l2 X1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l3 sK1 sK2 (sK1 ◇ sK2) X1]
  have l5 : ∀ X1 sK1 sK2 sK0 X0 sK3 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0))) = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X1 sK1 sK2 sK0 X0 sK3
    conv => enter [1]; rw [l4 X1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [h53905 sK2 sK1 sK3 (sK2 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ X1 sK1 sK2 sK0 X0 sK3 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0))) = ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK1 sK2 sK0 X0 sK3
    conv => enter [1]; rw [l5 X1 sK1 sK2 sK0 X0 sK3]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l7 : ∀ sK1 X1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X1 sK2 sK3 sK0
    conv => enter [1]; rw [h53905 sK1 X1 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [l6 X1 sK1 sK2 sK0 sK1 sK3]
  have l8 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 1]; rw [l7 sK1 sK2 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 X0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK2 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) X0]
  have l10 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [h53905 sK2 sK1 sK3 (sK2 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK2 X0 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1 (sK1 ◇ sK2) sK2 sK1 sK1]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2 sK2 sK1 sK1]
    conv => enter [1]; rw [← l7 sK1 (sK1 ◇ sK2) sK2 sK1 sK1]
  have l14 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53905 X0 (sK1 ◇ (sK1 ◇ sK2)) X0 X0]
    conv => enter [1]; rw [l12 sK1 sK2 (X0 ◇ (X0 ◇ X0))]
  have l15 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1]; rw [← l14 X0 sK1 sK2]
  have l16 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l15 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l17 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l16 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 X1 X0 (X0 ◇ X1) (sK1 ◇ (sK1 ◇ sK2))]
  have l18 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [h53905 sK2 X0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l18 x y z w]

theorem Equation4512_53953_implies_Equation53905 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53953 : Equation53953 G) : Equation53905 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK3 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l0 sK1 sK2 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l2 sK1 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0]
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h53953 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 sK1 X0]
  have l5 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) ◇ X1) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1) ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [l4 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1) X1]
  have l6 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) ◇ X1) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ X1))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 X1]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) ◇ X1) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h53953 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X1]
    conv => enter [1]; rw [← l6 sK1 sK2 sK3 sK0 X0 X1]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) X1]
  have l9 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK3 ◇ sK0)) X0 X1]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 (sK1 ◇ sK1)]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l4 sK1 sK2 sK3 sK0 X0]
  have l13 : ∀ sK2 X1 X2 sK1 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ X1)) = (X2 ◇ (X1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK2 X1 X2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [h53953 sK2 X1 X2 ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK2 (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l14 : ∀ sK2 sK1 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK3 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53953 X0 (sK1 ◇ (sK3 ◇ sK0)) sK2 X1]
  have l15 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h53953 X0 (sK1 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l16 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l15 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← l14 sK2 sK1 sK3 sK0 X0 X1]
  have l17 : ∀ sK2 X1 sK1 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ X1)) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1)) := by
    intro sK2 X1 sK1 sK3 sK0
    conv => enter [1]; rw [l13 sK2 X1 sK2 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h53953 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X1 sK2 sK2]
  have l18 : ∀ sK1 sK2 sK3 sK0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X1
    conv => enter [1]; rw [l16 sK1 sK2 sK3 sK0 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) X1]
    conv => enter [1]; rw [← l17 sK2 X1 sK1 sK3 sK0]
  have l19 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l16 sK1 sK2 sK3 sK0 X1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h53953 X0 X1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l19 sK1 sK2 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK1 sK2 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l19 sK1 sK2 sK1 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [← l19 sK1 sK2 sK1 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [l19 sK1 sK2 sK1 sK1 sK1 sK2]
  have l22 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l21 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l23 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK2 X0]
    conv => enter [1]; rw [← l19 sK1 sK2 sK3 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l24 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l23 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l18 sK1 sK2 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
  have l25 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l24 sK1 sK2 X0 sK1 sK1]
  have l26 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l25 sK1 sK2 (X1 ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [← h53953 X0 X1 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l27 : ∀ sK1 sK2 X2 X1 X0 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro sK1 sK2 X2 X1 X0 X3
    conv => enter [1]; rw [l26 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h53953 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l27 x y y x z w]

theorem Equation4512_53905_implies_Equation53962 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53962 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = (((sK0 ◇ sK1) ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 (sK0 ◇ sK1)]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 sK0 ((sK1 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [l1 sK0 sK1 sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ X0) X1]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l7 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 sK2 (sK0 ◇ sK1) X0 X1]
  have l8 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l9 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l8 sK2 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) sK0 sK2 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK0))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 ((sK1 ◇ sK2) ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK2 sK0 sK1]
  have l11 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h53905 sK2 (sK0 ◇ sK1) (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l12 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l11 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l13 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l12 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l14 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l13 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h53905 sK2 sK0 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ X0))) = (sK0 ◇ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0 X0]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ X0))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l17 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h53905 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l16 sK0 sK1 sK2 X0]
  have l18 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [← l17 sK2 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK1) ◇ (((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l17 sK2 sK0 sK1 X0]
  have l20 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK1) ◇ (((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1)) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) X1]
  have l21 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l14 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2 X0 X1]
  have l22 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l21 sK2 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) X0 X1]
  have l23 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l17 sK2 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l22 sK2 sK0 sK1 sK2 sK2]
  have l24 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l23 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ sK0)]
  have l25 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l23 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK0) X0]
  have l26 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK0 ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l25 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 X0]
  have l27 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l24 sK1 sK2 sK0]
  have l28 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l26 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h53905 sK2 sK2 sK0 X0]
  have l29 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l28 sK2 sK0 sK1 X0]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l27 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK2 ◇ sK0)]
  have l31 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h53905 sK2 (sK0 ◇ sK1) sK2 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1 sK2]
  have l32 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l31 sK2 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK2 ◇ (sK0 ◇ sK1))]
  have l33 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l32 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l34 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l33 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l35 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h53905 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l34 sK2 sK0 sK1 X0]
  have l36 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l35 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [l29 sK2 sK0 sK1 sK2]
  have l37 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l36 sK2 sK0 sK1]
    conv => enter [1]; rw [← l28 sK2 sK0 sK1 X0]
  have l38 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l37 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l39 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l38 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l40 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l39 sK1 sK2 sK0 X0]
  have l41 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [h53905 sK2 X0 (sK2 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← l38 sK2 sK0 sK1 sK2]
  have l42 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) X1 (sK0 ◇ sK1) X0]
  have l43 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l44 : ∀ sK3 sK2 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK3)) := by
    intro sK3 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK2 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK2 ◇ (sK0 ◇ sK1)) sK3 X0 X1]
  have l45 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l40 sK1 sK2 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h53905 (sK2 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK2) sK1 sK1]
  have l46 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l45 sK1 sK2 sK0]
    conv => enter [1]; rw [l18 sK2 sK0 sK1 (sK1 ◇ sK2)]
  have l47 : ∀ sK3 sK2 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l44 sK3 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l18 sK2 sK0 sK1 sK3]
  have l48 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0))) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l42 X1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l43 sK1 sK2 (sK1 ◇ sK2) X1]
  have l49 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l46 sK1 sK2 sK0]
    conv => enter [1]; rw [← h53905 sK2 sK2 sK2 (sK0 ◇ sK1)]
  have l50 : ∀ sK3 sK2 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l47 sK3 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h53905 sK2 sK2 sK2 (sK0 ◇ sK1)]
  have l51 : ∀ sK1 sK2 sK0 X1 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK1 sK2 sK0 X1 X0
    conv => enter [1]; rw [← l41 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [← l48 X1 sK1 sK2 sK0 X0]
  have l52 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l36 sK2 sK0 sK1]
    conv => enter [1]; rw [← l49 sK1 sK2 sK0]
  have l53 : ∀ sK3 sK2 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l50 sK3 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l36 sK2 sK0 sK1]
  have l54 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l51 sK1 sK2 sK0 X1 sK1]
    conv => enter [1]; rw [← h53905 sK1 X1 (sK2 ◇ (sK0 ◇ sK1)) sK1]
  have l55 : ∀ sK1 sK2 sK0 X1 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l54 sK1 sK2 sK0 X1]
  have l56 : ∀ sK2 sK0 sK1 X1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [l52 sK2 sK0 sK1]
    conv => enter [1]; rw [l55 sK1 sK2 sK0 X1]
  have l57 : ∀ sK2 sK0 sK1 X0 sK3 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK0 sK1 X0 sK3
    conv => enter [1]; rw [← l53 sK3 sK2 sK0 sK1 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h53905 X0 (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK2 sK2]
  have l58 : ∀ sK2 sK0 sK1 X0 X1 sK3 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK2 sK0 sK1 X0 X1 sK3
    conv => enter [1]; rw [l57 sK2 sK0 sK1 (X0 ◇ X1) sK3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK3 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l59 : ∀ X1 X0 sK2 sK0 sK1 : G, (X1 ◇ (X1 ◇ X0)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 sK2 sK0 sK1
    conv => enter [1]; rw [h53905 X1 X0 (X0 ◇ X1) (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l58 sK2 sK0 sK1 X0 X1 X1]
  have l60 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l59 sK2 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [h53905 sK2 X0 sK0 sK1]
  have l61 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← l56 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [l60 sK2 sK0 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [l61 x y z w]

theorem Equation4512_53962_implies_Equation53905 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53962 : Equation53962 G) : Equation53905 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X0)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h53962 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ X0))]
  have l1 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h53962 sK2 sK1 X0 sK1]
    conv => enter [1]; rw [h53962 sK2 sK1 X1 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h53962 (sK1 ◇ (sK1 ◇ sK2)) X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← h53962 sK2 sK1 sK1 sK1]
  have l3 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h53962 sK1 sK2 X1 sK2]
    conv => enter [1, 2]; rw [h53962 sK2 sK1 X0 sK1]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 X0 sK2]
    conv => enter [1]; rw [← l2 sK1 sK2 X0 sK1]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l1 (sK1 ◇ sK2) sK1 sK2 X0]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK2 sK1]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [← l7 sK1 sK2 X0]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK2 (X1 ◇ (sK1 ◇ X0))]
    conv => enter [1]; rw [← h53962 X0 X1 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l10 : ∀ X2 X1 X3 X0 sK1 sK2 : G, (X2 ◇ (X1 ◇ (X3 ◇ X0))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X2 X1 X3 X0 sK1 sK2
    conv => enter [1]; rw [← h53962 X0 X1 X2 X3]
    conv => enter [1]; rw [l9 X0 X1 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l10 y x z w x y]

theorem Equation4512_53905_implies_Equation53966 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53966 G := by
  have l0 : ∀ sK2 sK3 sK1 sK0 X0 : G, ((sK2 ◇ sK3) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK2 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK3 (sK1 ◇ sK0)]
  have l1 : ∀ sK2 sK3 sK1 sK0 X0 : G, ((sK2 ◇ sK3) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [l0 sK2 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ X1 sK2 sK3 sK1 sK0 X0 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0))) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X1)) := by
    intro X1 sK2 sK3 sK1 sK0 X0
    conv => enter [1, 2]; rw [← l1 sK2 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK2 ◇ sK3) X1 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK3 sK2 X0 X1]
  have l4 : ∀ X1 sK2 sK3 sK1 sK0 X0 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0))) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro X1 sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [l2 X1 sK2 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [l3 sK2 sK3 (sK2 ◇ sK3) X1]
  have l5 : ∀ X1 sK2 sK3 sK1 sK0 X0 sK4 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0))) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))))) := by
    intro X1 sK2 sK3 sK1 sK0 X0 sK4
    conv => enter [1]; rw [l4 X1 sK2 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [h53905 sK3 sK2 sK4 (sK3 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ X1 sK2 sK3 sK1 sK0 X0 sK4 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ (sK1 ◇ sK0)) ◇ X0))) = ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK2 sK3 sK1 sK0 X0 sK4
    conv => enter [1]; rw [l5 X1 sK2 sK3 sK1 sK0 X0 sK4]
    conv => enter [1]; rw [h4512 sK2 sK3 (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
  have l7 : ∀ sK2 X1 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ X1)) = ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 X1 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h53905 sK2 X1 (sK3 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [l6 X1 sK2 sK3 sK1 sK0 sK2 sK4]
  have l8 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = ((sK2 ◇ sK3) ◇ ((sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1, 1]; rw [l7 sK2 sK3 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))) X0]
  have l9 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l8 sK2 sK3 X0 sK2 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 sK3 (sK2 ◇ (sK3 ◇ (sK2 ◇ sK2))) X0]
  have l10 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l9 sK2 sK3 X0]
    conv => enter [1]; rw [h53905 sK3 sK2 sK4 (sK3 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK3 X0 sK4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 sK3 (sK4 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
  have l12 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l11 sK2 sK3 X0 sK2 sK2 sK2]
    conv => enter [1]; rw [← l7 sK2 (sK2 ◇ sK3) sK3 sK2 sK2 sK2]
  have l13 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l7 sK2 sK3 sK3 sK2 sK2 sK2]
    conv => enter [1]; rw [← l7 sK2 (sK2 ◇ sK3) sK3 sK2 sK2 sK2]
  have l14 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h53905 X0 (sK2 ◇ (sK2 ◇ sK3)) X0 X0]
    conv => enter [1]; rw [l12 sK2 sK3 (X0 ◇ (X0 ◇ X0))]
  have l15 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l13 sK2 sK3]
    conv => enter [1]; rw [← l14 X0 sK2 sK3]
  have l16 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK2 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l15 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK2 ◇ (sK2 ◇ sK3)))]
  have l17 : ∀ sK2 sK3 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l16 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h53905 X1 X0 (X0 ◇ X1) (sK2 ◇ (sK2 ◇ sK3))]
  have l18 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l17 sK2 sK3 sK3 X0]
    conv => enter [1]; rw [h53905 sK3 X0 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l18 x y z w u]

theorem Equation4512_53966_implies_Equation53905 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53966 : Equation53966 G) : Equation53905 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h53966 sK1 sK2 (X0 ◇ X1) sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK1 ◇ sK2))]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← h53966 sK1 sK2 sK1 sK1 sK2]
  have l2 : ∀ X3 X1 X4 X5 X0 sK1 sK2 : G, (X3 ◇ (X1 ◇ (X4 ◇ X5))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X3 X1 X4 X5 X0 sK1 sK2
    conv => enter [1]; rw [← h53966 X3 X1 X3 X4 X5]
    conv => enter [1]; rw [h53966 X3 X1 X0 sK1 (sK1 ◇ sK2)]
  have l3 : ∀ X3 X1 X4 X5 X0 sK1 sK2 : G, (X3 ◇ (X1 ◇ (X4 ◇ X5))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X3 X1 X4 X5 X0 sK1 sK2
    conv => enter [1]; rw [l2 X3 X1 X4 X5 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 X1]
  have l4 : ∀ sK1 sK2 X3 X1 X4 X5 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X3 ◇ (X1 ◇ (X4 ◇ X5))) := by
    intro sK1 sK2 X3 X1 X4 X5
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [← l3 X3 X1 X4 X5 sK1 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l4 x y y x z w]

end Semigroup5
